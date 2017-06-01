Require Import Automation.
Require Import Prog.
Require Import ProgTheorems.

(* TODO: document how specifications are structured *)

(** * refinement composition *)

(* A LRefinement (for "layer refinement") goes between State1 (implementation)
and State2 (spec) *)
Record LRefinement State1 State2 :=
  { abstraction : State1 -> State2 -> Prop; }.

(* TODO: come up with a good, short name for terms of type Refinement (currently
using [rf], which I'm not too happy with) *)
Definition Refinement State := LRefinement world State.

Definition IdRefinement State : LRefinement State State :=
  {| abstraction := fun state state' => state' = state; |}.

Definition refinement_compose
           `(rf1: Refinement State1)
           `(rf2: LRefinement State1 State2) :=
  {| abstraction := fun w state' => exists state, abstraction rf2 state state' /\
                                  abstraction rf1 w state; |}.

Record Quadruple T R State :=
  Spec {
      pre: Prop;
      post: T -> State -> Prop;
      recover: R -> State -> Prop;
    }.

Definition Specification A T R State := A -> State -> Quadruple T R State.

Generalizable Variable A.

Definition prog_spec `(spec: Specification A T R State) `(p: prog T)
           `(rec: prog R)
           `(rf: Refinement State) :=
  forall a w state,
    abstraction rf w state ->
    pre (spec a state) ->
    forall r, rexec p rec w r ->
         match r with
         | RFinished v w' => exists state',
                            abstraction rf w' state' /\
                            post (spec a state) v state'
         | Recovered v w' => exists state',
                            abstraction rf w' state' /\
                            recover (spec a state) v state'
         end.

Definition spec_impl
           `(spec1: Specification A' T R State)
           `(spec2: Specification A T R State) :=
  forall a state, pre (spec2 a state) ->
         exists a', pre (spec1 a' state) /\
               (forall v state', post (spec1 a' state) v state' ->
                        post (spec2 a state) v state') /\
               (forall rv state', recover (spec1 a' state) rv state' ->
                         recover (spec2 a state) rv state').

Theorem prog_spec_weaken : forall `(spec1: Specification A T R State)
                              `(spec2: Specification A' T R State)
                              `(p: prog T) `(rec: prog R)
                              (rf: Refinement State),
    prog_spec spec1 p rec rf ->
    spec_impl spec1 spec2 ->
    prog_spec spec2 p rec rf.
Proof.
  unfold prog_spec at 2; intros.
  eapply H0 in H2; eauto; repeat deex.
  eapply H in H3; eauto.
  destruct r; simpl in *; repeat deex; intuition eauto.
Qed.

Hint Resolve tt.

Theorem prog_spec_rx : forall `(spec: Specification A T R State)
                         `(p: prog T) `(rec: prog R)
                         `(rx: T -> prog T')
                         `(spec': Specification A' T' R State)
                         `(rf: Refinement State),
    prog_spec spec p rec rf ->
    (forall a' state, pre (spec' a' state) ->
             exists a, pre (spec a state) /\
                  (forall r,
                      prog_spec
                        (fun (_:unit) state' =>
                           {| pre := post (spec a state) r state';
                              post :=
                                fun r state'' =>
                                  post (spec' a' state) r state'';
                              recover :=
                                fun r state'' =>
                                  recover (spec' a' state) r state'' |})
                        (rx r) rec rf) /\
                  (forall r state', recover (spec a state) r state' ->
                           recover (spec' a' state) r state')) ->
    prog_spec spec' (Bind p rx) rec rf.
Proof.
  unfold prog_spec at 3; intros.
  inv_rexec.
  - inv_exec.
    match goal with
    | [ Hexec: exec p _ _ |- _ ] =>
      eapply RExec in Hexec
    end.
    eapply H0 in H2; repeat deex.
    eapply H in H9; simpl in *; safe_intuition (repeat deex; eauto).
    match goal with
    | [ Hexec: exec (rx _) _ _ |- _ ] =>
      eapply RExec in Hexec;
        eapply H3 in Hexec; eauto
    end.
  - inv_exec.
    + (* p crashed before running *)
      assert (exec p w' (Crashed w')) as Hexec by constructor.
      eapply RExecCrash in Hexec; eauto.
      eapply H0 in H2; repeat deex.
      eapply H in Hexec; simpl in *; safe_intuition (repeat deex; eauto).
    + (* p finished, rx crashed *)
      match goal with
      | [ Hexec: exec p _ _ |- _ ] =>
        eapply RExec in Hexec
      end.
      eapply H0 in H2; repeat deex.
      eapply H in H10; simpl in *; safe_intuition (repeat deex; eauto).
      match goal with
      | [ Hexec: exec (rx _) _ _ |- _ ] =>
        eapply RExecCrash in Hexec; eauto;
          eapply H3 in Hexec; eauto
      end.
    + (* p itself crashed *)
      match goal with
      | [ Hexec: exec p _ _ |- _ ] =>
        eapply RExecCrash in Hexec; eauto
      end.
      eapply H0 in H2; repeat deex.
      eapply H in H10; simpl in *; safe_intuition (repeat deex; eauto).
Qed.

(** * splitting spec into multiple cases *)

Theorem spec_cases : forall `(spec: Specification A T R State)
                       `(p: prog T) `(rec: prog R)
                       `(rf: Refinement State),
    (forall a state0,
        pre (spec a state0) ->
        prog_spec
          (fun (_:unit) state =>
             {| pre := state = state0;
                post :=
                  fun r state' => post (spec a state) r state';
                recover :=
                  fun r state' => recover (spec a state) r state';
             |}) p rec rf) ->
    prog_spec spec p rec rf.
Proof.
  unfold prog_spec at 2; intros.
  apply H in H1.
  eapply H1 in H2; eauto.
  simpl in *; eauto.
Qed.

Ltac spec_cases := intros; eapply spec_cases.

Ltac spec_case pf :=
  eapply prog_spec_weaken; [ solve [ apply pf ] |
                               unfold spec_impl ].

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

Definition prog_loopspec `(spec: Specification A unit unit State)
           `(rec': prog unit) `(rec: prog unit)
           (rf: Refinement State) :=
  forall a w state,
    abstraction rf w state ->
    pre (spec a state) ->
    forall rv rv' w',
      Relation_Operators.clos_refl_trans_1n
        (fun '(_, w) '(rv', w') => rexec rec' rec w (Recovered rv' w'))
        (rv, w) (rv', w') ->
      forall rv'' w'',
        exec rec' w' (Finished rv'' w'') ->
        exists state'',
          abstraction rf w'' state'' /\
          post (spec a state) rv'' state''.

Definition idempotent `(spec: Specification A T unit State) :=
  forall a state,
    pre (spec a state) ->
    forall v state', recover (spec a state) v state' ->
            (* idempotency: crash invariant implies precondition to
               re-run on every crash *)
            exists a', pre (spec a' state') /\
                  (* postcondition transitivity: establishing the
                     postcondition from a crash state is sufficient to
                     establish it with respect to the original initial
                     state (note all with the same ghost state) *)
                  forall rv state'', post (spec a' state') rv state'' ->
                                post (spec a state) rv state''.

Theorem idempotent_loopspec : forall `(rec: prog unit) `(rec': prog unit)
                                     `(spec: Specification A unit unit State)
                                     (rf: Refinement State),
    forall (Hspec: prog_spec spec rec' rec rf),
      idempotent spec ->
      prog_loopspec spec rec' rec rf.
Proof.
  unfold prog_loopspec; intros.
  apply clos_refl_trans_1n_unit_tuple in H2.
  repeat match goal with
         | [ u: unit |- _ ] => destruct u
         end.

  generalize dependent a.
  generalize dependent state.
  induction H2; intros.
  - eapply RExec in H3.
    eapply Hspec in H3; eauto.
  - eapply Hspec in H0; simpl in *; safe_intuition (repeat deex; eauto).
    eapply H in H4; eauto; repeat deex.
    specialize (H4 _ _ ltac:(eauto)); repeat deex; intuition.
    specialize (IHclos_refl_trans_1n _ ltac:(eauto) _ ltac:(eauto)).
    safe_intuition (repeat deex; eauto).
Qed.

Theorem compose_recovery : forall `(spec: Specification A'' T unit State)
                             `(rspec: Specification A' unit unit State)
                             `(spec': Specification A T unit State)
                             `(p: prog T) `(rec: prog unit) `(rec': prog unit)
                             `(rf: Refinement State),
    forall (Hspec: prog_spec spec p rec rf)
      (Hrspec: prog_loopspec rspec rec' rec rf)
      (Hspec_spec':
         forall (a:A) state, pre (spec' a state) ->
                    exists (a'':A''),
                      pre (spec a'' state) /\
                      (forall v state', post (spec a'' state) v state' ->
                               post (spec' a state) v state') /\
                      (forall v state', recover (spec a'' state) v state' ->
                               exists a', pre (rspec a' state') /\
                                     forall v' state'',
                                       post (rspec a' state') v' state'' ->
                                       recover (spec' a state) v' state'')),
      prog_spec spec' p (_ <- rec; rec') rf.
Proof.
  intros.
  unfold prog_spec; intros.
  eapply Hspec_spec' in H0; safe_intuition;
    repeat deex.
  clear Hspec_spec'.
  destruct r.
  - match goal with
    | [ Hexec: rexec p _ _ _ |- _ ] =>
      eapply rexec_finish_any_rec in Hexec;
        eapply Hspec in Hexec
    end; simpl in *; intuition (repeat deex; eauto).
  - inv_rexec.
    match goal with
    | [ Hexec: exec_recover _ _ _ _ |- _ ] =>
      eapply exec_recover_bind_inv in Hexec
    end; repeat deex.
    match goal with
    | [ Hexec: exec_recover rec _ _ _ |- _ ] =>
      eapply RExecCrash in Hexec; eauto
    end; repeat deex.
    match goal with
    | [ Hexec: rexec p _ _ _ |- _ ] =>
      eapply Hspec in Hexec
    end; simpl in *; safe_intuition (repeat deex; eauto).
    (* H3: recover -> exists a' *)
    (* H6: recover *)
    eapply H3 in H6; repeat deex.
    match goal with
    | [ Hexec: exec rec' _ _ |- _ ] =>
      eapply Hrspec in Hexec
    end; simpl in *; safe_intuition (repeat deex; eauto).
Qed.

Theorem spec_refinement_compose :
  forall `(spec: Specification A T R State2)
    `(p: prog T) `(rec: prog R)
    `(rf2: LRefinement State1 State2)
    `(rf1: Refinement State1),
    prog_spec
      (fun '(a, state2) state =>
         {| pre := pre (spec a state2) /\
                   abstraction rf2 state state2;
            post :=
              fun v state' =>
                exists state2',
                  post (spec a state2) v state2' /\
                  abstraction rf2 state' state2';
            recover :=
              fun v state' =>
                exists state2',
                  recover (spec a state2) v state2' /\
                  abstraction rf2 state' state2'; |}) p rec rf1 ->
    prog_spec spec p rec (refinement_compose rf1 rf2).
Proof.
  intros.
  unfold prog_spec, refinement_compose;
    simpl; intros; safe_intuition (repeat deex).
  eapply (H (a, state)) in H2; simpl in *; eauto.
  destruct r; intuition (repeat deex; eauto).
Qed.

Definition rec_noop `(rec: prog R) `(rf: Refinement State) (wipe: State -> State -> Prop) :=
  forall T (v:T),
    prog_spec
      (fun (_:unit) state =>
         {| pre := True;
            post := fun r state' => r = v /\
                             state' = state;
            recover := fun _ state' => wipe state state'; |})
      (Ret v) rec rf.

(* for recovery proofs about pure programs *)

Theorem ret_spec : forall `(rf: Refinement State)
                     (wipe: State -> State -> Prop)
                     `(spec: Specification A T R State)
                     (v:T) (rec: prog R),
    rec_noop rec rf wipe ->
    (forall a state, pre (spec a state) ->
            post (spec a state) v state /\
            (* TODO: is it ok for this to be for all state'? *)
            forall state', wipe state state' ->
                  forall r, recover (spec a state) r state') ->
    prog_spec spec (Ret v) rec rf.
Proof.
  intros.
  unfold prog_spec; intros.
  eapply H in H3; simpl in *; eauto.
  eapply H0 in H2.
  destruct r; safe_intuition (repeat deex; eauto).
Qed.

Record crash_effect_valid `(rf: LRefinement State1 State2)
       (wipe1: State1 -> State1 -> Prop)
       (wipe2: State2 -> State2 -> Prop) :=
  { wipe_abstraction: forall w state state', wipe1 w state ->
                                abstraction rf state state' ->
                                exists w', abstraction rf w w' /\
                                      wipe2 w' state';
    wipe_abstraction': forall w w' state', abstraction rf w w' ->
                                  wipe2 w' state' ->
                                  exists state, wipe1 w state /\
                                       abstraction rf state state';
    wipe_trans: forall state state' state'', wipe2 state state' ->
                                wipe2 state' state'' ->
                                wipe2 state state''; }.

Definition wipe_valid
           `(rf: Refinement State)
           (wipe: State -> State -> Prop) :=
  crash_effect_valid rf (fun w w' => w' = world_crash w) wipe.


(* TODO: this is proven, but is it useful? *)
Theorem rec_noop_compose : forall `(rec: prog unit) `(rec2: prog unit)
                             `(rf1: Refinement State1)
                             (wipe1: State1 -> State1 -> Prop)
                             `(rf2: LRefinement State1 State2)
                             (wipe2: State2 -> State2 -> Prop)
                             (crash_invariant: State1 -> Prop),
    forall (Hwipe: crash_effect_valid rf2 wipe1 wipe2),
      rec_noop rec rf1 wipe1 ->
      prog_spec
        (fun (state0':State2) state =>
           {| pre := exists state0, abstraction rf2 state0 state0' /\
                               wipe1 state0 state;
              post :=
                fun _ state' => exists state0, abstraction rf2 state' state0 /\
                                   wipe2 state0' state0;
              recover :=
                fun _ state' => exists state0, abstraction rf2 state0 state0' /\
                                   wipe1 state0 state';
           |}) rec2 rec rf1 ->
      rec_noop (_ <- rec; rec2) (refinement_compose rf1 rf2) wipe2.
Proof.
  unfold rec_noop; intros.
  eapply spec_refinement_compose; simpl.
  eapply compose_recovery; eauto.
  - (* loopspec for rec2 *)
    eapply idempotent_loopspec; eauto.
    unfold idempotent; simpl; intuition eauto.
  - (* chain specifications *)
    simpl; intuition idtac.
    simpl in *.
    descend; intuition (subst; eauto).
    descend; intuition (repeat deex; eauto).
Qed.

Theorem spec_exec_equiv : forall `(spec: Specification A T R State)
                            (p p': prog T) `(rec: prog R)
                            `(rf: Refinement State),
    exec_equiv p p' ->
    prog_spec spec p' rec rf ->
    prog_spec spec p rec rf.
Proof.
  unfold prog_spec; intros.
  eapply H0; eauto.
  eapply rexec_equiv; eauto.
  symmetry; auto.
Qed.

Ltac monad_simpl :=
  repeat match goal with
         | |- prog_spec _ (Bind (Ret _) _) _ _ =>
           eapply spec_exec_equiv; [ apply monad_left_id | ]
         | |- prog_spec _ (Bind (Bind _ _) _) _ _ =>
           eapply spec_exec_equiv; [ apply monad_assoc | ]
         end.

Ltac step_prog :=
  match goal with
  | |- forall _, _ => intros; step_prog
  | |- prog_spec _ (Ret _) _ _ =>
    eapply ret_spec
  | |- prog_spec _ _ _ _ =>
    monad_simpl;
    eapply prog_spec_rx; [ solve [ eauto ] | ]
  | [ H: prog_spec _ ?p _ _
      |- prog_spec _ ?p _ _ ] =>
    eapply prog_spec_weaken; [ eapply H | unfold spec_impl ]
  end.
