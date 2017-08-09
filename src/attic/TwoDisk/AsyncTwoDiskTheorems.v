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

Theorem disks_rel_stable' : forall F0 F1 state,
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

Theorem stable_pointwise_rel : forall T T' (d: diskOf T)
                                 (rel: T -> T' -> Prop)
                                 (rel': T' -> T' -> Prop),
    (forall b, Stable (rel b) rel') ->
    Stable (pointwise_rel rel d) (pointwise_rel rel').
Proof.
  unfold Stable; intros.
  rename a into d'.
  rename a' into d''.
  pointwise.
Qed.

Theorem collapse_flush : forall h bs bs',
    collapsesTo h bs ->
    pflushBlock bs bs' ->
    collapsesTo h bs'.
Proof.
  simpl; intros.
  inversion H0; subst; clear H0; eauto.
  destruct H; simpl in *.
  erewrite curr_val_some_cache in * by eauto; subst.
  econstructor; simpl; eauto.
  apply durable_includes_current.
Qed.

Theorem covered_stable_pflush : forall d,
    Stable (covered d) pflush.
Proof.
  intros.
  eapply stable_pointwise_rel; intros.
  unfold Stable; intros.
  eauto using collapse_flush.
Qed.

Theorem missing_stable : forall A (rel: A -> A -> Prop),
    Stable missing rel.
Proof.
  unfold Stable, missing; eauto.
Qed.

Hint Resolve covered_stable_pflush.
Hint Resolve missing_stable.

Definition curr_val_eq {B} {async:AsyncBlock B} (b:block) : B -> Prop :=
  fun bs => curr_val bs = b.

Theorem covered_some_latest : forall (d: histdisk) (d': disk) a bs,
    d' a = Some bs ->
    covered d d' ->
    d a |= curr_val_eq (curr_val bs).
Proof.
  intros.
  pose proof (pointwise_rel_holds H0 a).
  destruct matches in *;
  destruct (d a) eqn:?; eauto.
  repeat simpl_match.
  destruct H1; eauto.
Qed.

Hint Resolve covered_some_latest.

Theorem covered_none : forall (d: histdisk) (d': disk) a F,
    d' a = None ->
    covered d d' ->
    d a |= F.
Proof.
  intros.
  destruct (d a) eqn:?; eauto.
  exfalso.
  eauto using same_size_disks_not_different, pointwise_sizes_eq.
Qed.

Hint Resolve covered_none.

Theorem covered_curr_val:
  forall (a : addr) (d : histdisk) (d' : disk) (b : blockstate),
    d' a = Some b ->
    covered d d' ->
    d a |= curr_val_eq (curr_val b).
Proof.
  intros.
  destruct (d a) eqn:?; simpl; auto.
  apply pointwise_rel_holds with (a:=a) in H0;
    repeat simpl_match.
  apply collapse_current in H0.
  auto.
Qed.

Hint Resolve covered_curr_val.

Theorem then_wipe_wipe0 : forall state state' F,
    TD.disk0 state |= F ->
    TD.wipe state state' ->
    TD.disk0 state' |= then_wipe F.
Proof.
  unfold TD.wipe, then_wipe; intros; subst.
  destruct state.
  destruct disk0, disk1; simpl in *; eauto.
Qed.

Theorem then_wipe_wipe1 : forall state state' F,
    TD.disk1 state |= F ->
    TD.wipe state state' ->
    TD.disk1 state' |= then_wipe F.
Proof.
  unfold TD.wipe, then_wipe; intros; subst.
  destruct state.
  destruct disk0, disk1; simpl in *; eauto.
Qed.

Hint Resolve then_wipe_wipe0 then_wipe_wipe1.
Hint Resolve then_wipe_covered.

Theorem TDRead0_ok : forall (i: Interface TD.API) a,
    proc_spec
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state |= covered d_0 /\
                  TD.disk1 state |= F /\
                  Stable F pflush;
           post :=
             fun r state' =>
               match r with
               | Working v => TD.disk0 state' |= covered d_0 /\
                             TD.disk1 state' |= F /\
                             d_0 a |= curr_val_eq v
               | Failed => TD.disk0 state' |= missing /\
                          TD.disk1 state' |= F
               end;
           recover :=
             fun _ state' => TD.disk0 state' |= crashesTo d_0 /\
                      TD.disk1 state' |= then_wipe F;
         |})
      (Prim i (TD.Read d0 a))
      (irec i)
      (interface_abs i).
Proof.
  prim.
  destruct matches in *; cleanup.
  - eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - assert (TD.disk0 state'0 |= missing) by eauto.
    clear H0.
    eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - eapply pred_weaken; eauto.
  - destruct matches in *; cleanup;
      eauto using pred_weaken.
Qed.

Theorem TDRead1_ok : forall (i: Interface TD.API) a,
    proc_spec
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state |= F /\
                  TD.disk1 state |= covered d_1 /\
                  Stable F pflush;
           post :=
             fun r state' =>
               match r with
               | Working v => TD.disk0 state' |= F /\
                             TD.disk1 state' |= covered d_1 /\
                             d_1 a |= curr_val_eq v
               | Failed => TD.disk0 state' |= F /\
                          TD.disk1 state' |= missing
               end;
           recover :=
             fun _ state' => TD.disk0 state' |= then_wipe F /\
                      TD.disk1 state' |= crashesTo d_1;
         |})
      (Prim i (TD.Read d1 a))
      (irec i)
      (interface_abs i).
Proof.
  prim.
  destruct matches in *; cleanup.
  - eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - assert (TD.disk1 state'0 |= missing) by eauto.
    clear H5.
    eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - eapply pred_weaken; eauto.
  - destruct matches in *; cleanup;
      eauto using pred_weaken.
Qed.

(* TODO: move proofs somewhere more appropriate *)

Theorem pointwise_rel_indomain : forall B B' (rel: B -> B' -> Prop)
                                 (d: diskOf B) (d': diskOf B'),
    size d = size d' ->
    (forall a bs bs', a < size d ->
                 d a = Some bs ->
                 d' a = Some bs' ->
                 rel bs bs') ->
    pointwise_rel rel d d'.
Proof.
  intros.
  econstructor; intros; eauto.
  destruct matches; eauto using same_size_disks_not_different.
  eapply H0; eauto.
  pose proof (diskMem_domain d a).
  destruct matches in *.
  unfold disk_get in *; congruence.
Qed.

Hint Resolve collapsesTo_buffer.

Theorem covered_diskUpd_buffer : forall d d' a b,
    covered d d' ->
    covered (diskUpdF d a (buffer b)) (diskUpdF d' a (buffer b)).
Proof.
  unfold covered; intros.
  eapply pointwise_rel_indomain; autorewrite with upd in *; intros.
  eauto using pointwise_sizes_eq.
  apply pointwise_rel_holds with (a:=a0) in H.
  destruct matches in *; try contradiction.
  is_eq a a0.
  - try erewrite diskUpdF_eq in * by eauto;
      repeat match goal with
             | [ H: Some _ = Some _ |- _ ] =>
               inversion H; subst; clear H
             end.
    eauto.
  - autorewrite with upd in *.
    congruence.
  - exfalso; eauto using disk_inbounds_not_none.
Qed.

Hint Resolve covered_diskUpd_buffer.

Theorem TDWrite0_ok : forall (i: Interface TD.API) a b,
    proc_spec
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state |= covered d_0 /\
                  TD.disk1 state |= F /\
                  Stable F pflush;
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
               (TD.disk0 state' |= crashesTo d_0 \/
                a < size d_0 /\
                TD.disk0 state' |= crashesTo (diskUpdF d_0 a (buffer b))) /\
               TD.disk1 state' |= then_wipe F;
         |})
      (Prim i (TD.Write d0 a b))
      (irec i)
      (interface_abs i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.

  destruct (lt_dec a (size d_0));
    autorewrite with upd in *;
    eauto using pred_weaken.
  destruct matches in *; cleanup;
    try solve [ left + right; eauto using pred_weaken ].
  destruct (lt_dec a (size d_0));
    autorewrite with upd in *;
    eauto using pred_weaken.
  right; eauto using pred_weaken.
Qed.

Theorem TDWrite1_ok : forall (i: Interface TD.API) a b,
    proc_spec
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state |= F /\
                  TD.disk1 state |= covered d_1 /\
                  Stable F pflush;
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
               TD.disk0 state' |= then_wipe F /\
               (TD.disk1 state' |= crashesTo d_1 \/
                a < size d_1 /\
                TD.disk1 state' |= crashesTo (diskUpdF d_1 a (buffer b)));
         |})
      (Prim i (TD.Write d1 a b))
      (irec i)
      (interface_abs i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.

  destruct (lt_dec a (size d_1));
    autorewrite with upd in *;
    eauto using pred_weaken.
  destruct matches in *; cleanup;
    try solve [ left + right; eauto using pred_weaken ].
  destruct (lt_dec a (size d_1));
    autorewrite with upd in *;
    eauto using pred_weaken.
  right; eauto using pred_weaken.
Qed.

Theorem covered_size_eq' : forall d d',
    covered d d' ->
    size d' = size d.
Proof.
  intros.
  symmetry; eauto using pointwise_sizes_eq.
Qed.

Hint Resolve covered_size_eq'.

Theorem TDDiskSize0_ok : forall (i: Interface TD.API),
    proc_spec
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state |= covered d_0 /\
                  TD.disk1 state |= F /\
                  Stable F pflush;
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
               TD.disk0 state' |= crashesTo d_0 /\
               TD.disk1 state' |= then_wipe F;
         |})
      (Prim i (TD.DiskSize d0))
      (irec i)
      (interface_abs i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eauto using pred_weaken.
  destruct matches in *; cleanup;
    eauto using pred_weaken.
Qed.

Theorem TDDiskSize1_ok : forall (i: Interface TD.API),
    proc_spec
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state |= F /\
                  TD.disk1 state |= covered d_1 /\
                  Stable F pflush;
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
               TD.disk0 state' |= then_wipe F /\
               TD.disk1 state' |= crashesTo d_1;
         |})
      (Prim i (TD.DiskSize d1))
      (irec i)
      (interface_abs i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eauto using pred_weaken.
  destruct matches in *; cleanup;
    eauto using pred_weaken.
Qed.

(* TODO: simplify this proof *)
Theorem then_flush_covered : forall d d',
    then_flush (covered d) d' ->
    covered (flush d) d'.
Proof.
  unfold then_flush; intros; repeat deex.
  autounfold with disk in *; pointwise.
  assert (curr_val b0 = b1).
  destruct b0; simpl in *; subst; auto.
  apply collapse_current in H.
  econstructor; autorewrite with block in *; simpl; eauto.
  congruence.
  replace (current_val b) with b1 by congruence.
  unfold Ensemble.In; auto.
  apply collapse_current in H.
  econstructor; autorewrite with block in *; simpl; eauto.
  destruct b0; simpl in *; subst.
  autorewrite with block in *; subst.
  unfold Ensemble.In; auto.
Qed.

Theorem maybe_holds_then_flush : forall F md d,
    md |= F ->
    md = Some d ->
    then_flush F (flush d).
Proof.
  unfold then_flush.
  intros; subst; simpl in *.
  exists d; intuition eauto.
Qed.

Hint Resolve maybe_holds_then_flush.

Theorem stable_then_flush_pflush : forall F,
    Stable (then_flush F) pflush.
Proof.
  unfold Stable, then_flush; intros.
  repeat deex.
  exists d; intuition.
  eapply flushed_pflush in H0; eauto.
Qed.

Hint Resolve stable_then_flush_pflush.

Theorem pflush_blockstate_uncached : forall (bs bs': blockstate),
    cache_val bs = None ->
    pflush_blockstate bs bs' ->
    bs = bs'.
Proof.
  inversion 2; subst; eauto.
  congruence.
Qed.

Theorem wipeBlockstate_cacheval_none : forall bs,
    cache_val (wipeBlockstate bs) = None.
Proof.
  destruct bs; auto.
Qed.

Hint Resolve wipeBlockstate_cacheval_none.

Theorem then_wipe_then_flush : forall F d,
    then_wipe (then_flush F) d ->
    then_flush F d.
Proof.
  unfold then_wipe, then_flush; intros; repeat deex.
  exists d; intuition.
  autorewrite with flush; auto.
Qed.

Hint Resolve then_wipe_then_flush.

Theorem TDSync0_ok : forall (i: Interface TD.API),
    proc_spec
      (fun '(F0, F1) state =>
         {|
           pre := TD.disk0 state |= F0 /\
                  TD.disk1 state |= F1 /\
                  Stable F1 pflush;
           post :=
             fun r state' =>
               TD.disk0 state' |= then_flush F0 /\
               TD.disk1 state' |= F1;
           recover :=
             fun _ state' =>
               (TD.disk0 state' |= then_wipe F0 /\
                TD.disk1 state' |= then_wipe F1) \/
               (TD.disk0 state' |= then_flush F0 /\
                TD.disk1 state' |= then_wipe F1);
         |})
      (Prim i (TD.Sync d0))
      (irec i)
      (interface_abs i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  right; intuition.
  eapply pred_weaken; eauto.
  eapply pred_weaken; eauto.
Qed.

Theorem TDSync1_ok : forall (i: Interface TD.API),
    proc_spec
      (fun '(F0, F1) state =>
         {|
           pre := TD.disk0 state |= F0 /\
                  TD.disk1 state |= F1 /\
                  Stable F0 pflush;
           post :=
             fun r state' =>
               TD.disk0 state' |= F0 /\
               TD.disk1 state' |= then_flush F1;
           recover :=
             fun _ state' =>
               (TD.disk0 state' |= then_wipe F0 /\
                TD.disk1 state' |= then_wipe F1) \/
               (TD.disk0 state' |= then_wipe F0 /\
                TD.disk1 state' |= then_flush F1);
         |})
      (Prim i (TD.Sync d1))
      (irec i)
      (interface_abs i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  right; intuition.
  eapply pred_weaken; eauto.
  eapply pred_weaken; eauto.
Qed.

Theorem then_wipe_missing : forall md,
    md |= then_wipe missing ->
    md |= missing.
Proof.
  unfold then_wipe, missing; intros.
  destruct md; simpl in *; repeat deex; eauto.
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
