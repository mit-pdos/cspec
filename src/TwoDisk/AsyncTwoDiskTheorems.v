Require Import Automation.
Require Import MaybeHolds.

Require Import Refinement.ProgLang.Hoare.
Require Import Disk.AsyncDisk.
Require Import TwoDisk.TwoDiskDefs.
Require Import TwoDisk.AsyncTwoDiskAPI.

Require Import Refinement.Interface.

(* help out type inference *)
Implicit Type (state:TD.State).

Theorem maybe_holds_stable : forall state state' F0 F1,
    TD.disk0 state |= F0 ->
    TD.disk1 state |= F1 ->
    TD.bg_failure state state' ->
    TD.disk0 state' |= F0 /\
    TD.disk1 state' |= F1.
Proof.
  intros.
  TD.inv_failure; simpl in *; eauto.
Qed.

Ltac cleanup :=
  repeat match goal with
         | [ |- forall _, _ ] => intros
         | |- _ /\ _ => split; [ solve [ eauto || congruence ] | ]
         | |- _ /\ _ => split; [ | solve [ eauto || congruence ] ]
         | [ H: Working _ = Working _ |- _ ] => inversion H; subst; clear H
         | [ H: TD.bg_failure _ _ |- _ ] =>
           eapply maybe_holds_stable in H;
           [ | solve [ eauto ] | solve [ eauto ] ]; destruct_ands
         | [ H: _ |= covered _, H': _ = Some _ |- _ ] =>
                  pose proof (holds_some_inv_eq _ H' H); clear H
         | _ => deex
         | _ => destruct_tuple
         | _ => progress simpl in *
         | _ => progress unfold pre_step, post_step in *
         | _ => progress subst
         | _ => progress safe_intuition
         | _ => solve [ eauto ]
         | _ => congruence
         end.

Ltac prim :=
  intros; eapply prim_spec; cleanup;
  try TD.inv_step;
  try solve [ destruct matches in *; cleanup ].

Hint Resolve holds_in_some_eq.
Hint Resolve holds_in_none_eq.
Hint Resolve pred_missing.

Definition Stable A (P: A -> Prop) (R: A -> A -> Prop) :=
  forall a, P a ->
       forall a', R a a' -> P a'.

Theorem disks_rel_stable : forall F0 F1 R,
    Stable F0 R ->
    Stable F1 R ->
    Stable (fun state => TD.disk0 state |= F0 /\
                  TD.disk1 state |= F1) (TD.disks_rel R).
Proof.
  unfold Stable; intros; safe_intuition.
  match goal with
  | [ H: TD.disks_rel _ _ _ |- _ ] =>
    inversion H; subst; clear H; simpl in *
  end; intuition eauto.
Qed.

Lemma disks_rel_stable' : forall F0 F1 state,
    TD.disk0 state |= F0 ->
    TD.disk1 state |= F1 ->
    forall R, Stable F0 R ->
         Stable F1 R ->
         forall state', TD.disks_rel R state state' ->
               TD.disk0 state' |= F0 /\
               TD.disk1 state' |= F1.
Proof.
  intros.
  eapply disks_rel_stable in H3; eauto.
Qed.

Theorem covered_stable_pflushed : forall d,
    Stable (covered d) pflushed.
Proof.
  unfold Stable; intros.
  rename a into d'.
  rename a' into d''.
  destruct H.
  inversion H0; subst.
  econstructor; intros.
  congruence.
  specialize (H1 a).
  simpl_match.
  destruct (d' a) eqn:?; try contradiction.
  etransitivity; eauto.
Qed.

Theorem missing_stable : forall A (rel: A -> A -> Prop),
    Stable missing rel.
Proof.
  unfold Stable, missing; eauto.
Qed.

Hint Resolve covered_stable_pflushed.
Hint Resolve missing_stable.

Lemma covered_some_latest : forall (d d': disk) a bs,
    d' a = Some bs ->
    covered d d' ->
    d a |= (fun bs' => latest bs' = latest bs).
Proof.
  intros.
  destruct (d a) eqn:?; eauto.
  pose proof (covers_pointwise H0 a).
  simpl.
  eapply covers_latest_eq; eauto.
Qed.

Hint Resolve covered_some_latest.

Lemma covered_none : forall (d d': disk) a F,
    d' a = None ->
    covered d d' ->
    d a |= F.
Proof.
  intros.
  destruct (d a) eqn:?; eauto.
  exfalso.
  eauto using same_size_disks_not_different, covered_size_eq.
Qed.

Hint Resolve covered_none.

Theorem TDRead0_ok : forall (i: Interface TD.API) a,
    prog_spec
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state |= covered d_0 /\
                  TD.disk1 state |= F /\
                  Stable F pflushed;
           post :=
             fun r state' =>
               match r with
               | Working v => TD.disk0 state' |= covered d_0 /\
                             TD.disk1 state' |= F /\
                             d_0 a |= (fun bs => latest bs = v)
               | Failed => TD.disk0 state' |= missing /\
                          TD.disk1 state' |= F
               end;
           recover :=
             fun _ state' => TD.disk0 state' |= covered d_0 /\
                      TD.disk1 state' |= F;
         |})
      (Prim i (TD.Read d0 a))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  assert (TD.disk0 state'0 |= missing) by eauto.
  clear H0.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
Qed.

Theorem TDRead1_ok : forall (i: Interface TD.API) a,
    prog_spec
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state |= F /\
                  TD.disk1 state |= covered d_1 /\
                  Stable F pflushed;
           post :=
             fun r state' =>
               match r with
               | Working v => TD.disk0 state' |= F /\
                             TD.disk1 state' |= covered d_1 /\
                             d_1 a |= (fun bs => latest bs = v)
               | Failed => TD.disk0 state' |= F /\
                          TD.disk1 state' |= missing
               end;
           recover :=
             fun _ state' => TD.disk0 state' |= F /\
                      TD.disk1 state' |= covered d_1;
         |})
      (Prim i (TD.Read d1 a))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  assert (TD.disk1 state'0 |= missing) by eauto.
  clear H5.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
Qed.

(* TODO: move proofs somewhere more appropriate *)

Lemma covers_buffer : forall b bs bs',
    covers bs bs' ->
    covers (buffer b bs) (buffer b bs').
Proof.
  intros.
  inversion H; subst; simpl in *.
  econstructor; intros; eauto.
  simpl in *; intuition eauto.
  eapply H0 in H2; intuition eauto.
Qed.

Hint Resolve covers_buffer.

Lemma covered_diskUpd_buffer : forall d d' a b,
    covered d d' ->
    covered (diskUpdF d a (buffer b)) (diskUpdF d' a (buffer b)).
Proof.
  intros.
  destruct H.
  econstructor; intros; eauto.
  autorewrite with upd; auto.
  is_eq a a0; autorewrite with upd in *; eauto.
  rename a0 into a.
  destruct (lt_dec a (size d)).
  - pose proof (@diskUpdF_inbounds _ d a (buffer b) ltac:(auto));
      repeat deex.
    assert (a < size d') by congruence.
    pose proof (@diskUpdF_inbounds _ d' a (buffer b) ltac:(auto));
      repeat deex.
    pose proof (covers_pointwise _ _ _ ltac:(eauto) ltac:(eauto)).
    repeat match goal with
           | [ H: ?a = Some _,
                  H': ?a = Some _ |- _ ] =>
             rewrite H in H'; inversion H'; subst
           end.
    eauto.
  - autorewrite with upd in *.
    congruence.
Qed.

Hint Resolve covered_diskUpd_buffer.

Theorem TDWrite0_ok : forall (i: Interface TD.API) a b,
    prog_spec
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state |= covered d_0 /\
                  TD.disk1 state |= F /\
                  Stable F pflushed;
           post :=
             fun r state' =>
               match r with
               | Working _ => TD.disk0 state' |= covered (diskUpdF d_0 a (buffer b)) /\
                             TD.disk1 state' |= F
               | Failed => TD.disk0 state' |= missing /\
                          TD.disk1 state' |= F
               end;
           recover :=
             fun _ state' =>
               (TD.disk0 state' |= covered d_0 \/
                a < size d_0 /\ TD.disk0 state' |= covered (diskUpdF d_0 a (buffer b))) /\
               TD.disk1 state' |= F;
         |})
      (Prim i (TD.Write d0 a b))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.

  destruct matches in *; cleanup.
  destruct (lt_dec a (size d_0));
    autorewrite with upd in *;
    eauto.
Qed.

Theorem TDWrite1_ok : forall (i: Interface TD.API) a b,
    prog_spec
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state |= F /\
                  TD.disk1 state |= covered d_1 /\
                  Stable F pflushed;
           post :=
             fun r state' =>
               match r with
               | Working _ => TD.disk0 state' |= F /\
                             TD.disk1 state' |= covered (diskUpdF d_1 a (buffer b))
               | Failed => TD.disk0 state' |= F /\
                          TD.disk1 state' |= missing
               end;
           recover :=
             fun _ state' =>
               TD.disk0 state' |= F /\
               (TD.disk1 state' |= covered d_1 \/
                a < size d_1 /\ TD.disk1 state' |= covered (diskUpdF d_1 a (buffer b)));
         |})
      (Prim i (TD.Write d1 a b))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.

  destruct matches in *; cleanup.
  destruct (lt_dec a (size d_1));
    autorewrite with upd in *;
    eauto.
Qed.

Lemma covered_size_eq' : forall d d',
    covered d d' ->
    size d' = size d.
Proof.
  intros.
  symmetry; eauto using covered_size_eq.
Qed.

Hint Resolve covered_size_eq'.

Theorem TDDiskSize0_ok : forall (i: Interface TD.API),
    prog_spec
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state |= covered d_0 /\
                  TD.disk1 state |= F /\
                  Stable F pflushed;
           post :=
             fun r state' =>
               match r with
               | Working n => n = size d_0 /\
                             TD.disk0 state' |= covered d_0 /\
                             TD.disk1 state' |= F
               | Failed => TD.disk0 state' |= missing /\
                          TD.disk1 state' |= F
               end;
           recover :=
             fun _ state' =>
               TD.disk0 state' |= covered d_0 /\
               TD.disk1 state' |= F;
         |})
      (Prim i (TD.DiskSize d0))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
Qed.

Theorem TDDiskSize1_ok : forall (i: Interface TD.API),
    prog_spec
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state |= F /\
                  TD.disk1 state |= covered d_1 /\
                  Stable F pflushed;
           post :=
             fun r state' =>
               match r with
               | Working n => n = size d_1 /\
                             TD.disk0 state' |= F /\
                             TD.disk1 state' |= covered d_1
               | Failed => TD.disk0 state' |= F /\
                          TD.disk1 state' |= missing
               end;
           recover :=
             fun _ state' =>
               TD.disk0 state' |= F /\
               TD.disk1 state' |= covered d_1;
         |})
      (Prim i (TD.DiskSize d1))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
Qed.

Lemma maybe_holds_then_flush : forall F md d,
    md |= F ->
    md = Some d ->
    then_flush F (flush d).
Proof.
  intros; subst; simpl in *.
  eauto.
Qed.

Hint Resolve maybe_holds_then_flush.

Lemma stable_then_flush_pflushed : forall F,
    Stable (then_flush F) pflushed.
Proof.
  unfold Stable, then_flush; intros.
  repeat deex.
  exists d; intuition.
  etransitivity; eauto using pflushed_is_covered.
Qed.

Hint Resolve stable_then_flush_pflushed.

Theorem TDSync0_ok : forall (i: Interface TD.API),
    prog_spec
      (fun '(F0, F1) state =>
         {|
           pre := TD.disk0 state |= F0 /\
                  TD.disk1 state |= F1 /\
                  Stable F1 pflushed;
           post :=
             fun r state' =>
               TD.disk0 state' |= then_flush F0 /\
               TD.disk1 state' |= F1;
           recover :=
             fun _ state' =>
               (TD.disk0 state' |= F0 /\
                TD.disk1 state' |= F1) \/
               (TD.disk0 state' |= then_flush F0 /\
                TD.disk1 state' |= F1);
         |})
      (Prim i (TD.Sync d0))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
Qed.

Theorem TDSync1_ok : forall (i: Interface TD.API),
    prog_spec
      (fun '(F0, F1) state =>
         {|
           pre := TD.disk0 state |= F0 /\
                  TD.disk1 state |= F1 /\
                  Stable F0 pflushed;
           post :=
             fun r state' =>
               TD.disk0 state' |= F0 /\
               TD.disk1 state' |= then_flush F1;
           recover :=
             fun _ state' =>
               (TD.disk0 state' |= F0 /\
                TD.disk1 state' |= F1) \/
               (TD.disk0 state' |= F0 /\
                TD.disk1 state' |= then_flush F1);
         |})
      (Prim i (TD.Sync d1))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
Qed.

Hint Resolve
     TDRead0_ok
     TDRead1_ok
     TDWrite0_ok
     TDWrite1_ok
     TDDiskSize0_ok
     TDDiskSize1_ok
     TDSync0_ok
     TDSync1_ok.
