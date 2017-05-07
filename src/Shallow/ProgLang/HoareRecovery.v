Require Import Automation.
Require Import Prog.
Require Import ProgTheorems.
Require Import Hoare.

Set Implicit Arguments.

Record RecQuadruple T R State :=
  RecSpec {
      rec_pre: Prop;
      rec_post: T -> State -> Prop;
      recover_post: R -> State -> Prop;
    }.

Definition RecSpecification A T R State := A -> State -> RecQuadruple T R State.

Definition prog_rspec `(spec: RecSpecification A T R State) `(p: prog opT T) `(rec: prog opT R)
           `(step: Semantics opT State) :=
  forall a state,
    rec_pre (spec a state) ->
    forall r, rexec step p rec state r ->
         match r with
         | RFinished v state' => rec_post (spec a state) v state'
         | Recovered v state' => recover_post (spec a state) v state'
         end.

Definition prog_loopspec
           `(spec: Specification A R State)
           `(rec: prog opT R)
           `(step: Semantics opT State) :=
  forall a state, pre (spec a state) ->
         forall rv state', exec_recover step rec state rv state' ->
                  post (spec a state) rv state'.

Theorem prog_loopspec_weaken
        `(spec1: Specification A1 R State)
        `(spec2: Specification A2 R State)
        `(rec: prog opT R)
        `(step: Semantics opT State) :
  prog_loopspec spec1 rec step ->
  forall (Himpl: spec_impl spec1 spec2),
    prog_loopspec spec2 rec step.
Proof.
  unfold prog_loopspec; intros.
  eapply Himpl in H0; repeat deex; eauto.
Qed.

(* TODO: generalize this definition to allow changes to ghost state (but the
original somehow still has to show up) *)
Definition idempotent `(spec: Specification A R State) :=
  (* idempotency: crash invariant implies precondition to re-run on every
  crash *)
  (forall a state, pre (spec a state) ->
          forall state', crash (spec a state) state' ->
                pre (spec a state')) /\
  (* postcondition transitivity: establishing the postcondition from a crash
  state is sufficient to establish it with respect to the original initial state
  (note all with the same ghost state) *)
  (forall a state,
      pre (spec a state) ->
      forall state' rv state'',
        crash (spec a state) state' ->
        post (spec a state') rv state'' ->
        post (spec a state) rv state'').

Lemma idempotent_loopspec : forall `(spec: Specification A R State)
                              `(rec: prog opT R)
                              `(step: Semantics opT State),
    forall (Hspec: prog_spec spec rec step),
      idempotent spec ->
      prog_loopspec spec rec step.
Proof.
  unfold idempotent, prog_loopspec; intuition.
  induction H2.
  - eapply Hspec in H2; eauto.
  - eapply Hspec in H2; eauto.
Qed.

Theorem prog_spec_from_crash : forall `(spec: RecSpecification A T R State)
                                 `(p: prog opT T) `(rec: prog opT R)
                                 (step: Semantics opT State)
                                 `(pspec: Specification A1 T State)
                                 `(rspec: Specification A2 R State),
    forall (Hpspec: prog_spec pspec p step)
      (Hrspec: prog_loopspec rspec rec step),
      (forall a state, rec_pre (spec a state) ->
              (* program's precondition holds *)
              exists a1, pre (pspec a1 state) /\
                    (* within same ghost state, normal postcondition is correct *)
                    (forall v state', post (pspec a1 state) v state' ->
                             rec_post (spec a state) v state') /\
                    (* crash invariant allows running recovery *)
                    (forall state', crash (pspec a1 state) state' ->
                           exists a2, pre (rspec a2 state') /\
                                 (* and recovery establishes recovery postcondition *)
                                 (forall rv state'', post (rspec a2 state') rv state'' ->
                                                recover_post (spec a state) rv state'') /\
                                 (forall state'', crash (rspec a2 state') state'' ->
                                             pre (rspec a2 state'')))) ->
      prog_rspec spec p rec step.
Proof.
  unfold prog_rspec, prog_loopspec; intuition.
  inversion H1; subst.
  - eapply H in H0; eauto.
    deex.
    eapply Hpspec in H2; eauto.
  - eapply H in H0; eauto.
    deex.
    eapply Hpspec in H2; eauto.
    eapply H5 in H2.
    deex.
    eauto.
Qed.
