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
           `(rf: Refinement State) :=
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
           `(rf: Refinement State) :=
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
        `(rf: Refinement State) :
  prog_loopspec spec1 rec rf ->
  forall (Himpl: spec_impl spec1 spec2),
    prog_loopspec spec2 rec rf.
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
                              `(rf: Refinement State),
    forall (Hspec: prog_spec spec rec rf),
      idempotent spec ->
      prog_loopspec spec rec rf.
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
                                  `(pspec: Specification A1 T State)
                                  `(rspec: Specification A2 R State),
    forall (Hpspec: prog_spec pspec p rf)
      (Hrspec: prog_loopspec rspec rec rf),
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
      prog_rspec spec p rec rf.
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
                              (rf: Refinement State),
    prog_rspec spec1 p rec rf ->
    rspec_impl spec1 spec2 ->
    prog_rspec spec2 p rec rf.
Proof.
  unfold prog_rspec at 2; intros.
  eapply H0 in H1; eauto; repeat deex.
  eapply H in H3; eauto.
  destruct r; simpl in *; intuition eauto.
Qed.

Definition RecDoublePre T R State :=
  (* initial state *)
  State ->
  (* postcondition *)
  (T -> State -> Prop) ->
  (* recovery postcondition *)
  (R -> State -> Prop) ->
  Prop.

Definition prog_rdouble `(pre: RecDoublePre T R State)
           `(p: prog T) `(rec: prog R)
           (rf: Refinement State) :=
  forall w postcond recpost,
    let state := abstraction rf w in
    pre state postcond recpost ->
    invariant rf w ->
    forall r, rexec p rec w r ->
         match r with
         | RFinished v w' => let state' := abstraction rf w' in
                            postcond v state' /\
                            invariant rf w'
         | Recovered v w' => let state' := abstraction rf w' in
                            recpost v state' /\
                            invariant rf w'
         end.

Definition prog_rok `(spec: RecSpecification A T R State)
           `(p: prog T) `(rec: prog R)
           `(rf: Refinement State) :=
  forall T' (rx: T -> prog T'),
    prog_rdouble
      (fun state postcond recpost =>
         exists a, rec_pre (spec a state) /\
              (forall r, prog_rdouble
                      (fun state' postcond' recpost' =>
                         rec_post (spec a state) r state' /\
                         postcond' = postcond /\
                         recpost' = recpost)
                      (rx r) rec rf) /\
              (forall r state', recover_post (spec a state) r state' ->
                       recpost r state')) (Bind p rx) rec rf.

Theorem rdouble_weaken : forall `(p: prog T) `(rec: prog R)
                          `(rf: Refinement State)
                          (pre pre': RecDoublePre T R State),
    prog_rdouble pre' p rec rf ->
    (forall state postcond recpost, pre state postcond recpost ->
                           pre' state postcond recpost) ->
    prog_rdouble pre p rec rf.
Proof.
  unfold prog_rdouble at 2; intros.
  eapply H; eauto.
Qed.

Theorem prog_rspec_to_rok : forall `(spec: RecSpecification A T R State)
                              `(p: prog T) `(rec: prog R)
                              `(rf: Refinement State),
    prog_rspec spec p rec rf ->
    prog_rok spec p rec rf.
Proof.
  unfold prog_rok, prog_rdouble; intros.
  repeat deex.
  destruct r.
  - inv_rexec.
    inv_exec.
    repeat match goal with
           | [ H: exec _ _ _ |- _ ] =>
             eapply RExec with (rec:=rec) in H
           end.
    match goal with
    | [ Hexec: rexec p _ _ (RFinished _ _) |- _ ] =>
      eapply H in Hexec; simpl in *; safe_intuition eauto
    end.
    specialize (H3 v0 w' postcond recpost); safe_intuition.
    eapply H3 in H12; eauto.
  - eapply rexec_recover_bind_inv in H2; hyp_intuition.
    + match goal with
      | [ Hexec: rexec p _ _ (Recovered _ _) |- _ ] =>
        eapply H in Hexec; simpl in *; safe_intuition eauto
      end.
    + repeat deex.
      match goal with
      | [ Hexec: rexec p _ _ (RFinished _ _) |- _ ] =>
        eapply H in Hexec; simpl in *; safe_intuition eauto
      end.
      specialize (H3 v0 w' postcond recpost); safe_intuition.
      eapply H3 in H5; eauto.
Qed.

(* TODO: the return value is actually unconstrained here, so this will really
   only work for unit-producing recovery procedures.

   We really don't have a story for return values from recovery yet, but I'm
   hesitant to get rid of them everywhere in case we find a way to use them.
 *)
Definition rec_noop `(rec: prog R) `(rf: Refinement State) :=
  prog_spec
    (fun (_:unit) state =>
       {| pre := True;
          post := fun _ state' => state' = state;
          crash := fun state' => state' = state; |}) rec rf.

Theorem rec_noop_loop `(rec: prog R) `(rf: Refinement State) :
  rec_noop rec rf ->
  prog_loopspec
    (fun (_:unit) state =>
       {| pre := True;
          post := fun _ state' => state' = state;
          crash := fun state' => state' = state; |}) rec rf.
Proof.
  unfold rec_noop; intros.
  apply idempotent_loopspec; auto.
  unfold idempotent; simpl in *; intros.
  subst; eauto.
Qed.

Hint Resolve tt.

Theorem prog_rok_to_rspec : forall `(spec: RecSpecification A T R State)
                              `(p: prog T) `(rec: prog R)
                              `(rf: Refinement State),
    prog_rok spec p rec rf ->
    rec_noop rec rf ->
    (forall a state, rec_pre (spec a state) ->
           forall v state',
             rec_post (spec a state) v state' ->
             forall rv, recover_post (spec a state) rv state') ->
    prog_rspec spec p rec rf.
Proof.
  unfold prog_rok, prog_rdouble, prog_rspec; intros.
  eapply rec_noop_loop in H0.
  specialize (H _ Ret).
  specialize (H w).
  eapply H; eauto.
  exists a; intuition eauto; subst.
  - inv_rexec; inv_ret; eauto.
    (* recovery after finishing p *)
    match goal with
    | [ Hexec: exec_recover _ _ _ _ |- _ ] =>
      eapply H0 in Hexec; simpl in *; safe_intuition eauto
    end.
    replace (abstraction rf w'').
    intuition eauto.
  - eapply rexec_equiv.
    apply monad_right_id.
    eauto.
Qed.

Theorem rdouble_exec_equiv : forall `(rf: Refinement State)
                              `(pre: RecDoublePre T R State) (p p': prog T)
                              (rec: prog R),
    exec_equiv p p' ->
    prog_rdouble pre p' rec rf ->
    prog_rdouble pre p rec rf.
Proof.
  unfold prog_rdouble; intros.
  eapply H0 in H1; eauto.
  eapply rexec_equiv; eauto.
  symmetry; auto.
Qed.

Ltac monad_simpl ::=
  repeat match goal with
         | |- prog_rdouble _ (Bind (Ret _) _) _ _ =>
           eapply rdouble_exec_equiv; [ apply monad_left_id | ]
         | |- prog_rdouble _ (Bind (Bind _ _) _) _ _ =>
           eapply rdouble_exec_equiv; [ apply monad_assoc | ]
         end.

(** step_prog_with t handles the first program in a bind by applying tactic t *)
Ltac step_prog_with t ::=
  match goal with
  | |- prog_rdouble _ _ _ _ =>
    monad_simpl;
    eapply rdouble_weaken; [ solve [ t ] | ]
  | |- forall _, _ => intros; step_prog_with t
  | |- prog_rok _ _ _ _ => unfold prog_rok; step_prog_with t
  end.

(** step_prog applies a registered prog_ok theorem (in the prog hint database)
to the first program in a sequence of binds. *)
Ltac step_prog ::= step_prog_with ltac:(eauto with prog).

(* similar notation to Hoare.v's, this time for recovery Extern hints

   TODO: make this notation nicer;
   I don't like making the only distinction three braces instead of two, but
   also don't know where to put a keyword to distinguish them that doesn't look
   terrible.
 *)
Notation "{{{ p ; '_' }}}" := (prog_rdouble _ (Bind p _) _ _)
                              (only parsing, at level 0).

(** * (much simpler) alternative to begin *)

Theorem rdouble_cases : forall `(pre: RecDoublePre T R State)
                          `(p: prog T) `(rec: prog R)
                          `(rf: Refinement State),
    (forall state postcond recpost,
        pre state postcond recpost ->
        exists pre', prog_rdouble pre' p rec rf /\
                pre' state postcond recpost) ->
    prog_rdouble pre p rec rf.
Proof.
  unfold prog_rdouble at 2; intros.
  apply H in H0; repeat deex.
  eapply H0; eauto.
Qed.

Ltac rdouble_case pf :=
  eexists; split; [ solve [ apply pf ] | ].

(* for recovery proofs about pure programs *)

Theorem ret_prog_rok : forall `(rf: Refinement State)
                         `(spec: RecSpecification A T R State)
                         (v:T) (rec: prog R),
    rec_noop rec rf ->
    (forall a state, rec_pre (spec a state) ->
            rec_post (spec a state) v state /\
            forall r, recover_post (spec a state) r state) ->
    prog_rok spec (Ret v) rec rf.
Proof.
  intros.
  unfold prog_rok, prog_rdouble; intros.
  repeat deex.
  eapply H0 in H1; intuition eauto.
  apply rexec_bind_cases in H3; hyp_intuition;
    repeat deex.
  - inv_rexec; inv_exec.
    eapply H4; eauto.
  - inv_rexec; inv_exec.
    eapply rec_noop_loop in H.
    match goal with
    | [ Hexec: exec_recover rec _ _ _ |- _ ] =>
      eapply H in Hexec; simpl in *; safe_intuition eauto
    end.
    replace (abstraction rf w'').
    eauto.
Qed.

(** * Proving a higher-level recovery procedure correct. *)

Hint Constructors rexec.
Hint Constructors exec.
Hint Constructors exec_recover.

Lemma clos_refl_trans_1n_unit_tuple : forall A (R: unit * A -> unit * A -> Prop) x y u u',
    Relation_Operators.clos_refl_trans_1n R (u, x) (u', y) ->
    Relation_Operators.clos_refl_trans_1n
      (fun x y =>
         R (tt, x) (tt, y)) x y.
Proof.
  intros.
  destruct u, u'.
  remember (tt, x).
  remember (tt, y).
  generalize dependent x.
  generalize dependent y.
  induction H; intuition subst.
  - inversion Heqp0; subst.
    inversion Heqp; subst.
    constructor.
  - destruct y.
    destruct u.
    especialize IHclos_refl_trans_1n; safe_intuition.
    especialize IHclos_refl_trans_1n; safe_intuition.
    econstructor; eauto.
Qed.

Definition prog_rec_loopspec `(spec: RecSpecification A unit unit State)
           `(rec': prog unit) `(rec: prog unit)
           (rf: Refinement State) :=
  forall a w,
    let state := abstraction rf w in
    rec_pre (spec a state) ->
    invariant rf w ->
    forall rv rv' w',
      Relation_Operators.clos_refl_trans_1n
        (fun '(_, w) '(rv', w') => rexec rec' rec w (Recovered rv' w'))
        (rv, w) (rv', w') ->
      forall rv'' w'',
        exec rec' w' (Finished rv'' w'') ->
        let state'' := abstraction rf w'' in
        rec_post (spec a state) rv'' state'' /\
        invariant rf w''.

Definition rec_idempotent `(spec: RecSpecification A T unit State) :=
  forall a state,
    rec_pre (spec a state) ->
    forall v state', recover_post (spec a state) v state' ->
          (* idempotency: crash invariant implies precondition to re-run on
               every crash *)
          exists a', rec_pre (spec a' state') /\
                (* postcondition transitivity: establishing the postcondition
                   from a crash state is sufficient to establish it with respect
                   to the original initial state (note all with the same ghost
                   state) *)
                forall rv state'', rec_post (spec a' state') rv state'' ->
                              rec_post (spec a state) rv state''.

Theorem rec_idempotent_loopspec : forall `(rec: prog unit) `(rec': prog unit)
                                    `(spec: RecSpecification A unit unit State)
                                    (rf: Refinement State),
    forall (Hspec: prog_rspec spec rec' rec rf),
      rec_idempotent spec ->
      prog_rec_loopspec spec rec' rec rf.
Proof.
  unfold prog_rec_loopspec; intros.
  apply clos_refl_trans_1n_unit_tuple in H2.
  repeat match goal with
         | [ u: unit |- _ ] => destruct u
         end.

  generalize dependent a.
  induction H2; intros.
  - eapply RExec in H3.
    eapply Hspec in H3; eauto.
  - eapply Hspec in H0; simpl in *; safe_intuition eauto.
    eapply H in H0; eauto; repeat deex.
    specialize (IHclos_refl_trans_1n a'); intuition eauto.
Qed.

Theorem compose_recovery : forall `(spec: RecSpecification A'' T unit State)
                             `(rspec: RecSpecification A' unit unit State)
                             `(spec': RecSpecification A T unit State)
                             `(p: prog T) `(rec: prog unit) `(rec': prog unit)
                             `(rf: Refinement State),
    forall (Hspec: prog_rspec spec p rec rf)
      (Hrspec: prog_rec_loopspec rspec rec' rec rf)
      (Hspec_spec':
         forall (a:A) state, rec_pre (spec' a state) ->
                exists (a'':A''),
                  rec_pre (spec a'' state) /\
                  (forall v state', rec_post (spec a'' state) v state' ->
                           rec_post (spec' a state) v state') /\
                  (forall v state', recover_post (spec a'' state) v state' ->
                           exists a', rec_pre (rspec a' state') /\
                                 forall v' state'',
                                   rec_post (rspec a' state') v' state'' ->
                                   recover_post (spec' a state) v' state'')),
      prog_rspec spec' p (_ <- rec; rec') rf.
Proof.
  intros.
  unfold prog_rspec; intros.
  eapply Hspec_spec' in H; safe_intuition.
  destruct r.
  - repeat deex.
    match goal with
    | [ Hexec: rexec p _ _ _ |- _ ] =>
      eapply rexec_finish_any_rec in Hexec;
        eapply Hspec in Hexec
    end; simpl in *; intuition eauto.
  - inv_rexec.
    match goal with
    | [ Hexec: exec_recover _ _ _ _ |- _ ] =>
      eapply exec_recover_bind_inv in Hexec
    end; repeat deex.
    assert (rexec p rec w (Recovered rv1 w1)) by eauto.
    (* H7: exec p *)
    (* H1: exec_recover rec *)
    clear H7 H1.
    match goal with
    | [ Hexec: rexec p _ _ _ |- _ ] =>
      eapply Hspec in Hexec
    end; simpl in *; safe_intuition eauto.
    (* H5: recover_post -> exists a' *)
    (* H1: recover_post *)
    eapply H5 in H1; repeat deex.
    match goal with
    | [ Hexec: exec rec' _ _ |- _ ] =>
      eapply Hrspec in Hexec
    end; simpl in *; safe_intuition eauto.
Qed.

Theorem rspec_refinement_compose :
  forall `(spec: RecSpecification A T R State2)
    `(p: prog T) `(rec: prog R)
    `(rf2: LRefinement State1 State2)
    `(rf1: Refinement State1),
    prog_rspec
      (fun (a:A) state =>
         let state2 := layer_abstraction rf2 state in
         {| rec_pre := rec_pre (spec a state2) /\
                       layer_invariant rf2 state;
            rec_post :=
              fun v state' =>
                let state2' := layer_abstraction rf2 state' in
                rec_post (spec a state2) v state2' /\
                layer_invariant rf2 state';
            recover_post :=
              fun v state' =>
                let state2' := layer_abstraction rf2 state' in
                recover_post (spec a state2) v state2' /\
                layer_invariant rf2 state'; |}) p rec rf1 ->
    prog_rspec spec p rec (refinement_compose rf1 rf2).
Proof.
  intros.
  unfold prog_rspec, refinement_compose;
    simpl; intros; safe_intuition.
  eapply H in H2; simpl in *; eauto.
  destruct r; intuition eauto.
Qed.
