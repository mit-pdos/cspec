Require Import ProgLang.Prog.
Require Import ProgLang.ProgTheorems.
Require Import ProgLang.Hoare.
Require Import ProgLang.HoareRecovery.
Require Import Automation.

(* Language 1 is the implementation, language 2 is the spec:

 We will show that implementation executions have corresponding high-level
 executions, where the correspondence is given via an abstraction function. *)

Section Interpreter.
  Variables opT1 opT2: Type -> Type.
  Notation prog1 := (prog opT1).
  Notation prog2 := (prog opT2).

  Variable op_impl: forall T, opT2 T -> prog1 T.
  (* for now, recovery must make all changes to state and cannot preserve
     its return value

     TODO: for log, need to generalize this or have recovery store result in
     variable

     TODO: might want to allow recovery to return an error code and make no
     promises
   *)
  Variable rec: prog1 unit.

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

  Hypothesis
    (Hop_recover_ok: forall T (op:opT2 T),
        prog_rspec
          (fun (_:unit) state =>
             {|
               rec_pre := invariant state;
               rec_post :=
                 fun v state' => invariant state' /\
                          step2 op (abstraction state) v (abstraction state');
               recover_post :=
                 fun _ state' =>
                   invariant state' /\
                   (abstraction state' = abstraction state \/
                    exists v, step2 op (abstraction state) v (abstraction state'));
             |})
          (op_impl op)
          rec
          step1).

  (* This condition is required for two reasons:

   - there might be no operations, and recovery still has to work in that case
   - when we crash while running pure code, the recovery procedure really needs
     to not do anything to the abstraction

     The condition is fairly trivial because it almost follows from the recovery
     specs in Hop_recover_ok; in particular, it would actually follow from
     prog_rspec of any read-only operation. Unfortunately there's no guarantee
     there are any read-only operations; in practice, this theorem is likely to
     be a lemma for the recovery procedure in a realistic prog layer.
   *)
  Hypothesis
    (Hret_recover:
       prog_loopspec
         (fun (_:unit) state =>
            {|
              pre := invariant state;
              post :=
                fun v state' => invariant state' /\
                         abstraction state' = abstraction state;
              crash :=
                fun state' => invariant state' /\
                       abstraction state' = abstraction state;
            |})
         rec
         step1).

  Notation exec1 := (exec step1).
  Notation exec2 := (exec step2).
  Notation rexec1 := (rexec step1).
  Notation rexec2 := (rexec step2).

  Set Default Proof Using "All".

  Definition res_abstraction T (r: RResult State1 T unit) : Result State2 T :=
    match r with
    | RFinished v state => Finished v (abstraction state)
    | Recovered _ state => Crashed (abstraction state)
    end.

  Definition res_invariant T R (r: RResult State1 T R) : Prop :=
    match r with
    | RFinished _ state => invariant state
    | Recovered _ state => invariant state
    end.

  Theorem rexec_impl : forall T (op:opT2 T) state r,
      invariant state ->
      rexec1 (op_impl op) rec state r ->
      match r with
      | RFinished v state' =>
        invariant state' /\
        step2 op (abstraction state) v (abstraction state')
      | Recovered _ state' =>
        invariant state' /\
        (abstraction state' = abstraction state \/
         exists v, step2 op (abstraction state) v (abstraction state'))
      end.
  Proof.
    intros.
    eapply Hop_recover_ok in H0; simpl in *; intuition.
  Qed.

  Hint Constructors exec rexec.

  (* TODO: this property shouldn't be called interpretation, need a more
  intuitive name *)
  Definition interpretation :=
    forall T (p: prog2 T) state r,
      invariant state ->
      rexec1 (interpret p) rec state r ->
      exec2 p (abstraction state) (res_abstraction r) /\
      res_invariant r.

  Theorem interpret_exec : interpretation.
  Proof.
    unfold interpretation.
    induction p; simpl; intros.
    - eapply rexec_impl in H0; eauto.
      destruct r; simpl; intuition eauto.
      replace (abstraction state0); eauto.
      deex; eauto.
    - apply rexec_ret in H0.
      destruct r.
      + simpl; intuition (subst; eauto).
      + eapply Hret_recover in H0; simpl in *; safe_intuition; auto.
        replace (abstraction state0); eauto.
    - inversion H1; subst; simpl.
      + inv_exec.
        match goal with
        | [ Hexec: exec1 (interpret p) _ _ |- _ ] =>
          eapply RExec in Hexec;
            eapply IHp in Hexec; eauto; safe_intuition
        end.
        match goal with
        | [ Hexec: exec1 (interpret (p0 _)) _ _ |- _ ] =>
          eapply RExec in Hexec;
            eapply H in Hexec; eauto; safe_intuition
        end.
        intuition eauto.
      + eapply rexec_recover_bind_inv in H1; hyp_intuition; repeat deex.
        eapply IHp in H1; safe_intuition; eauto.
        eapply IHp in H1; safe_intuition; eauto.
        eapply H in H4; safe_intuition; eauto.
  Qed.

  Definition rres_abstraction `(r: RResult State1 T R) : RResult State2 T R :=
    match r with
    | RFinished v state => RFinished v (abstraction state)
    | Recovered v state => Recovered v (abstraction state)
    end.

  (* TODO: prove this more general correctness theorem to give some confidence
  that [interpretation] is enough to guarantee that even the higher-level
  recovery execution is correct. *)
  Definition interpretation_rexec :=
    forall T (p: prog2 T) R (rec2: prog2 R) state r,
      invariant state ->
      rexec1 (interpret p) (Bind rec (fun _ => interpret rec2)) state r ->
      rexec2 p rec2 (abstraction state) (rres_abstraction r) /\
      res_invariant r.

  Theorem interpret_rexec :
    interpretation -> interpretation_rexec.
  Proof.
    unfold interpretation, interpretation_rexec; intros.
    destruct r; simpl.
    - eapply rexec_finish_any_rec in H1.
      eapply H in H1; safe_intuition; eauto.
    - eapply rexec_rec_bind_inv in H1; repeat deex.
      eapply H in H1; simpl in *; safe_intuition; eauto.
      (* this output from [rexec_rec_bind_inv] is not quite what we need: we
         need to lift the interpretation statement to one about exec_recover by
         induction over the crashing executions, in order to show an
         [exec_recover step2] that is used to prove rexec2 here. *)
      admit.
  Abort.

End Interpreter.
