Require Import ProgLang.Prog.
Require Import ProgLang.ProgTheorems.
Require Import Automation.

(* Language 1 is the implementation, language 2 is the spec:

 We will show that implementation executions have corresponding high-level
 executions, where the correspondence is given via an abstraction function. *)

Section Interpreter.
  Variables opT1 opT2: Type -> Type.
  Notation prog1 := (prog opT1).
  Notation prog2 := (prog opT2).

  Variable op_impl: forall T, opT2 T -> prog1 T.

  Fixpoint interpret T (p: prog2 T) : prog1 T :=
    match p with
    | Prim op => op_impl op
    | Ret v => Ret v
    | Bind p p' => Bind (interpret p) (fun v => interpret (p' v))
    end.

  Variables State1 State2: Type.
  Variable step1: Semantics opT1 State1.
  Variable step2: Semantics opT2 State2.

  Variable invariant: State1 -> Prop.
  Variable abstraction: State1 -> State2.

  Notation exec1 := (exec step1).
  Notation exec2 := (exec step2).
  Notation rexec1 := (rexec step1).
  Notation rexec2 := (rexec step2).

  (* TODO: in general, it might not be the case that crash states line up with
  abstract states as desired; there might be states that are only exposed by
  recovery and that are then patched up during recovery. *)
  Definition res_abstraction T (r: Result State1 T) : Result State2 T :=
    match r with
    | Finished v state => Finished v (abstraction state)
    | Crashed state => Crashed (abstraction state)
    end.

  (* TODO: similar problem here, where there might be a weaker crash
  invariant *)
  Definition res_invariant T (r: Result State1 T) : Prop :=
    match r with
    | Finished _ state => invariant state
    | Crashed state => invariant state
    end.

  (* TODO: this property shouldn't be called interpretation, need a more
  intuitive name *)
  Definition interpretation :=
    forall T (p: prog2 T) state r,
      invariant state ->
      exec1 (interpret p) state r ->
      exec2 p (abstraction state) (res_abstraction r) /\
      res_invariant r.

  Hint Constructors exec.

  Theorem interpret_exec :
    (* every operation is implemented according to the step semantics of the
    spec language *)
    forall (Hop_ok: forall T (op: opT2 T) state v state',
          invariant state ->
          exec1 (op_impl op) state (Finished v state') ->
          step2 op (abstraction state) v (abstraction state') /\ invariant state')
      (* every implementation crashes in states that are abstractly either the
        pre state or the post state

        TODO: this is too strong, we only need this property after a crash
        transform and recovery; the intermediate states can satisfy some weaker
        crash invariant
       *)
      (Hop_crash: forall T (op: opT2 T) state state',
          invariant state ->
          exec1 (op_impl op) state (Crashed state') ->
          (abstraction state' = abstraction state \/
           exists v, step2 op (abstraction state) v (abstraction state')) /\
          invariant state'),
      interpretation.
  Proof.
    unfold interpretation.
    induction p; simpl; intros.
    - destruct r; simpl.
      + eapply Hop_ok in H0; eauto.
        intuition eauto.
      + eapply Hop_crash in H0; intuition eauto;
          repeat deex;
          eauto.
        replace (abstraction state0); eauto.
    - inv_exec; simpl; eauto.
    - inv_exec.
      + match goal with
        | [ Hexec: exec1 (interpret p) _ _ |- _ ] =>
          eapply IHp in Hexec; simpl in *; eauto; safe_intuition
        end.
        match goal with
        | [ Hexec: exec1 (interpret (p0 _)) _ _ |- _ ] =>
          eapply H in Hexec; eauto; safe_intuition
        end.
        intuition eauto.
      + match goal with
        | [ Hexec: exec1 (interpret p) _ _ |- _ ] =>
          eapply IHp in Hexec; simpl in *; eauto; safe_intuition
        end.
        intuition eauto.
  Qed.

  Definition rres_abstraction T R (r: RResult State1 T R) : RResult State2 T R :=
    match r with
    | RFinished v state => RFinished v (abstraction state)
    | Recovered v state => Recovered v (abstraction state)
    end.

  Definition rres_invariant T R (r: RResult State1 T R) : Prop :=
    match r with
    | RFinished _ state => invariant state
    | Recovered _ state => invariant state
    end.

  (* for now, recovery must make all changes to state and cannot preserve
     its return value

     TODO: for log, need to generalize this or have recovery store result in
     variable *)
  Variable rec: prog1 unit.

  Definition exec_recover_interpretation :=
    forall R (pr: prog2 R) state rv state',
      invariant state ->
      exec_recover step1 (Bind rec (fun _ => interpret pr)) state rv state' ->
      exec_recover step2 pr (abstraction state) rv (abstraction state') /\
      invariant state'.

  Definition rexec_interpretation :=
    forall T (p: prog2 T) R (pr: prog2 R) state r,
      invariant state ->
      rexec1 (interpret p) (Bind rec (fun _ => interpret pr)) state r ->
      rexec2 p pr (abstraction state) (rres_abstraction r) /\
      rres_invariant r.

  Hypothesis (Hinterp: interpretation).

  Hypothesis
      (Hrec: forall state r, exec step1 rec state r ->
                    (* TODO: should be crash invariant *)
                    invariant state ->
                    res_invariant r /\
                    match r with
                    | Finished _ state' =>
                      (* TODO: too strong - what the recovery procedure needs to
                         guarantee is that it preserves the crash abstractions
                         of [interpret p] (that is, when [state] is a crash state of
                         [interpret p], the recovery can produce [state'] with an
                         abstraction)

                         Note that this can be phrased as a per-operation
                         assumption that implies a property about all
                         interpreted programs. *)
                      abstraction state' = abstraction state
                    | Crashed state' =>
                      (* TODO: in this case, similar to Finished case we will
                      guarantee the abstraction is from some crash state, but
                      will not guarantee the invariant in res_invariant but only
                      the crash invariant (sufficient for idempotency) *)
                      abstraction state' = abstraction state
                    end).

  Set Default Proof Using "All".

  Ltac cleanup := simpl in *; eauto; safe_intuition;
                  try match goal with
                      | |- _ /\ _ =>
                        split; [ | solve [ eauto ]]
                      end.

  Hint Constructors exec_recover.

  Ltac forward_specs :=
    repeat match goal with
           | [ H: exec _ rec _ _ |- _ ] =>
             eapply Hrec in H; cleanup
           | [ H: exec _ (interpret _) _ _ |- _ ] =>
             eapply Hinterp in H; cleanup
           end;
    repeat match goal with
             (* TODO: this will have to be more sophisticated with proper
             recovery crash correctness handling *)
           | [ H: abstraction _ = abstraction _ |- _ ] =>
             rewrite H in *
           end;
    eauto.

  Theorem interpret_exec_recover : exec_recover_interpretation.
  Proof.
    unfold interpretation, exec_recover_interpretation; intros.
    induction H0.
    - inv_exec; forward_specs.
    - inv_exec; forward_specs.
  Qed.

  Hint Constructors rexec.

  Theorem interpret_rexec : rexec_interpretation.
  Proof.
    unfold interpretation, rexec_interpretation; intros.
    match goal with
    | [ H: rexec _ _ _ _ _ |- _ ] =>
      inversion H; subst; repeat sigT_eq
    end.
    - simpl; forward_specs.
    - simpl; forward_specs.
      eapply interpret_exec_recover in H2; cleanup.
      eauto.
  Qed.

End Interpreter.

Theorem interpretation_weaken : forall `(step1: Semantics opT1 State1)
                                  `(step2: Semantics opT2 State2)
                                  (step2': Semantics opT2 State2)
                                  op_impl
                                  invariant
                                  abstraction,
    semantics_impl step2 step2' ->
    interpretation op_impl step1 step2 invariant abstraction ->
    interpretation op_impl step1 step2' invariant abstraction.
Proof.
  unfold interpretation; intros.
  intuition.
  eapply exec_weaken; eauto.
  eapply H0; eauto.
  eapply H0; eauto.
Qed.
