Require Import Relations.Relation_Operators.

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
  intuitive name

     This statement defines trace refinement between any spec program [p] and
     its implementation, [interpret p], where each spec primitive is replaced
     with an implementation provided by [op_impl op]. We do not actually track
     any trace of operations (the primitives or some other events produced by
     the primitives); instead, the trace of a program is just its return value.

     Proving trace refinement directly for all states is not likely to be
     possible; instead, the implementation (that is, all of [op_impl]) can
     expect to run from certain "good" initial states and maintain some
     invariant during execution. We add this to the definition of trace
     refinement so it more obviously holds inductively.
   *)
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

  Definition interpretation_rexec :=
    forall T (p: prog2 T) R (rec2: prog2 R) state r,
      invariant state ->
      rexec1 (interpret p) (Bind rec (fun _ => interpret rec2)) state r ->
      rexec2 p rec2 (abstraction state) (rres_abstraction r) /\
      res_invariant r.

  Section ClosReflTransImp.

    Hint Constructors clos_refl_trans_1n.

    Lemma clos_refl_trans_1n_imp : forall A (R R':A -> A -> Prop) a a',
        clos_refl_trans_1n A R a a' ->
        (forall a a', R a a' -> R' a a') ->
        clos_refl_trans_1n A R' a a'.
    Proof.
      induction 1; intros; eauto.
    Qed.

  End ClosReflTransImp.

  Local Hint Constructors exec_recover.

  Lemma rexec2_exec2_star:
    forall (T : Type) (p : prog2 T) (R : Type) (rec2 : prog2 R) (state : State1)
      (v : R) (state0 : State1) (rv1 : unit) (state1 : State1) (rv2 : unit)
      (state2 : State1),
      invariant state1 ->
      exec2 (T:=T) p (abstraction state) (Crashed (abstraction state1)) ->
      clos_refl_trans_1n (unit * State1)
                         (fun '(_, state3) '(_, state') =>
                            invariant state3 ->
                            exec2 (T:=R) rec2 (abstraction state3) (Crashed (abstraction state')) /\ invariant state')
                         (rv1, state1) (rv2, state2) ->
      (invariant state2 ->
       exec2 (T:=R) rec2 (abstraction state2) (Finished v (abstraction state0)) /\
       invariant state0) ->
      rexec2 (R:=R) p rec2 (abstraction state) (Recovered v (abstraction state0)) /\
      invariant state0.
  Proof.
    intros.
    assert (exec_recover step2 rec2 (abstraction state1) v (abstraction state0) /\
            invariant state0).
    clear dependent H0.
    remember (rv1, state1).
    remember (rv2, state2).
    generalize dependent state0.
    generalize dependent state1.
    generalize dependent rv1.
    generalize dependent rv2.
    induction H1; intros; subst;
      repeat match goal with
             | [ H: (_, _) = (_, _) |- _ ] =>
               inversion H; subst; clear H
             end; eauto; safe_intuition.
    intuition eauto.
    destruct y; intuition eauto.
    econstructor 2; eauto.
    eapply IHclos_refl_trans_1n; eauto.
    eapply IHclos_refl_trans_1n; eauto.
    intuition eauto.
  Qed.

  Theorem interpret_rexec :
    interpretation_rexec.
  Proof.
    pose proof interpret_exec.
    unfold interpretation, interpretation_rexec in *; intros.
    destruct r; simpl.
    - eapply rexec_finish_any_rec in H1.
      eapply H in H1; safe_intuition; eauto.
    - inversion H1; subst.
      match goal with
      | [ H: exec_recover _ (Bind _ _) _ _ _ |- _ ] =>
        eapply exec_recover_bind_inv in H; eauto
      end.
      repeat deex.
      assert (rexec1 (interpret p) rec state (Recovered rv1 state1)) by eauto.
      eapply H in H5; eauto; safe_intuition; simpl in *.

      assert (clos_refl_trans_1n
                (unit * State1)
                (fun '(_, state) '(rv', state') =>
                   invariant state ->
                   exec2 rec2 (abstraction state) (Crashed (abstraction state')) /\
                   invariant state') (rv1, state1) (rv2, state2)).
      { eapply clos_refl_trans_1n_imp; eauto.
        destruct a, a'; intros.
        eapply H in H8; eauto. }
      assert (invariant state2 -> exec2 rec2 (abstraction state2) (Finished v (abstraction state0)) /\ invariant state0).
      intros.
      assert (rexec1 (interpret rec2) rec state2 (RFinished v state0)) by eauto.
      eapply H in H10; simpl in *; intuition eauto.

      eauto using rexec2_exec2_star.
  Qed.

End Interpreter.
