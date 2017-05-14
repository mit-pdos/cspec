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

Definition prog_rspec `(spec: RecSpecification A T R State) `(p: prog T)
           `(rec: prog R)
           `(rf: Refinement State)
           `(step: Semantics State) :=
  forall a w,
    let state := abstraction rf w in
    rec_pre (spec a state) ->
    invariant rf w ->
    forall r, rexec p rec w r ->
         match r with
         | RFinished v w' => let state' := abstraction rf w' in
                            rec_post (spec a state) v state' /\
                            invariant rf w'
         | Recovered v w' => let state' := abstraction rf w' in
                            recover_post (spec a state) v state' /\
                            invariant rf w'
         end.

Definition prog_loopspec
           `(spec: Specification A R State)
           `(rec: prog R)
           `(rf: Refinement State)
           `(step: Semantics State)
            :=
  forall a w, let state := abstraction rf w in
         pre (spec a state) ->
         invariant rf w ->
         forall rv w', exec_recover rec w rv w' ->
                  let state' := abstraction rf w' in
                  post (spec a state) rv state' /\
                  invariant rf w'.

Theorem prog_loopspec_weaken
        `(spec1: Specification A1 R State)
        `(spec2: Specification A2 R State)
        `(rec: prog R)
        `(rf: Refinement State)
        `(step: Semantics State) :
  prog_loopspec spec1 rec rf step ->
  forall (Himpl: spec_impl spec1 spec2),
    prog_loopspec spec2 rec rf step.
Proof.
  unfold prog_loopspec; intros.
  eapply Himpl in H0; repeat deex; eauto.
  eapply H in H2; intuition eauto.
Qed.

Definition idempotent `(spec: Specification A R State) :=
  forall a state,
    pre (spec a state) ->
    forall state', crash (spec a state) state' ->
          (* idempotency: crash invariant implies precondition to re-run on
               every crash *)
          exists a', pre (spec a' state') /\
                (* postcondition transitivity: establishing the postcondition
                   from a crash state is sufficient to establish it with respect
                   to the original initial state (note all with the same ghost
                   state) *)
                forall rv state'', post (spec a' state') rv state'' ->
                              post (spec a state) rv state''.

Lemma idempotent_loopspec : forall `(spec: Specification A R State)
                              `(rec: prog R)
                              `(rf: Refinement State)
                              `(step: Semantics State),
    forall (Hspec: prog_spec spec rec rf step),
      idempotent spec ->
      prog_loopspec spec rec rf step.
Proof.
  unfold idempotent, prog_loopspec; intros; safe_intuition.
  generalize dependent a.
  induction H2; intros.
  - match goal with
    | [ Hexec: exec _ _ (Finished _ _) |- _ ] =>
      eapply Hspec in Hexec; eauto
    end.
  - match goal with
    | [ Hexec: exec _ _ (Crashed _) |- _ ] =>
      eapply Hspec in Hexec; eauto
    end.
    simpl in *; safe_intuition.
    match goal with
    | [ Hpre: pre (spec _ _) |- _ ] =>
      eapply H in Hpre; repeat deex; eauto
    end.
    specialize (IHexec_recover a'); intuition eauto.
Qed.

Theorem prog_rspec_from_crash : forall `(spec: RecSpecification A T R State)
                                  `(p: prog T) `(rec: prog R)
                                  (rf: Refinement State)
                                  (step: Semantics State)
                                  `(pspec: Specification A1 T State)
                                  `(rspec: Specification A2 R State),
    forall (Hpspec: prog_spec pspec p rf step)
      (Hrspec: prog_loopspec rspec rec rf step),
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
                                                recover_post (spec a state) rv state''))) ->
      prog_rspec spec p rec rf step.
Proof.
  unfold prog_rspec, prog_loopspec; intuition.
  inversion H2; subst.
  - eapply H in H0; eauto.
    deex.
    eapply Hpspec in H3; eauto.
    simpl in *; intuition eauto.
  - eapply H in H0; eauto.
    deex.
    eapply Hpspec in H3; eauto.
    simpl in *; safe_intuition.
    eapply H6 in H3.
    deex.
    eapply Hrspec in H4; intuition eauto.
Qed.

Definition rspec_impl
           `(spec1: RecSpecification A' T R State)
           `(spec2: RecSpecification A T R State) :=
  forall a state, rec_pre (spec2 a state) ->
         exists a', rec_pre (spec1 a' state) /\
               (forall v state', rec_post (spec1 a' state) v state' ->
                        rec_post (spec2 a state) v state') /\
               (forall rv state', recover_post (spec1 a' state) rv state' ->
                         recover_post (spec2 a state) rv state').

Theorem prog_rspec_weaken : forall `(spec1: RecSpecification A T R State)
                              `(spec2: RecSpecification A' T R State)
                              `(p: prog T) `(rec: prog R)
                              (rf: Refinement State)
                              (step: Semantics State),
    prog_rspec spec1 p rec rf step ->
    rspec_impl spec1 spec2 ->
    prog_rspec spec2 p rec rf step.
Proof.
  unfold prog_rspec at 2; intros.
  eapply H0 in H1; eauto; repeat deex.
  eapply H in H3; eauto.
  destruct r; simpl in *; intuition eauto.
Qed.
