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

Theorem stable_pointwise_rel : forall T T' (d: diskOf T)
                                 (rel: T -> T' -> Prop)
                                 (rel': T' -> T' -> Prop),
    (forall b, Stable (rel b) rel') ->
    Stable (pointwise_rel rel d) (pointwise_rel rel').
Proof.
  unfold Stable; intros.
  rename a into d'.
  rename a' into d''.
  inversion_clear H0.
  inversion_clear H1.
  eapply pointwise_rel_indomain; intros; eauto.
  congruence.
  specialize (pointwise_rel_holds a).
  specialize (pointwise_rel_holds0 a).
  destruct matches in *; eauto; try contradiction.
Qed.

Theorem collapse_flush : forall h bs bs',
    collapsesTo h bs ->
    pflushBlock bs bs' ->
    collapsesTo h bs'.
Proof.
  simpl; intros.
  inversion H0; subst; clear H0; eauto.
  destruct H; simpl in *.
  erewrite curr_val_some_cache in * by eauto.
  econstructor; simpl; eauto.
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

Lemma covered_some_latest : forall (d: histdisk) (d': disk) a bs,
    d' a = Some bs ->
    covered d d' ->
    d a |= (fun bs' => curr_val bs' = curr_val bs).
Proof.
  intros.
  pose proof (pointwise_rel_holds H0 a).
  destruct matches in *;
  destruct (d a) eqn:?; eauto.
  repeat simpl_match.
  destruct H1; eauto.
Qed.

Hint Resolve covered_some_latest.

Lemma covered_none : forall (d: histdisk) (d': disk) a F,
    d' a = None ->
    covered d d' ->
    d a |= F.
Proof.
  intros.
  destruct (d a) eqn:?; eauto.
  exfalso.
  eauto using same_size_disks_not_different, sizes_eq.
Qed.

Hint Resolve covered_none.

Definition then_wipe (F: disk -> Prop) : disk -> Prop :=
  fun d' => exists d, F d /\ pflush (wipeDisk d) d'.

Theorem then_wipe_wipe : forall (F: disk -> Prop) d,
    F d ->
    then_wipe F (wipeDisk d).
Proof.
  unfold then_wipe; intros.
  descend; intuition eauto.
  reflexivity.
Qed.

Hint Resolve then_wipe_wipe.

Theorem then_wipe_crashesTo : forall d md,
    md |= then_wipe (covered d) ->
    md |= crashesTo d.
Proof.
  intros.
  eapply pred_weaken; intros; eauto.
  unfold then_wipe in *; repeat deex.
  eauto using wipe_crashesTo.
Qed.

Hint Resolve then_wipe_crashesTo.

Theorem disk0_wipe : forall state state' F,
    TD.disk0 state |= F ->
    TD.wipe state state' ->
    TD.disk0 state' |= then_wipe F.
Proof.
  unfold TD.wipe; intros; subst.
  destruct state; simpl in *.
  destruct matches; simpl in *; eauto.
Qed.

Theorem disk1_wipe : forall state state' F,
    TD.disk1 state |= F ->
    TD.wipe state state' ->
    TD.disk1 state' |= then_wipe F.
Proof.
  unfold TD.wipe; intros; subst.
  destruct state; simpl in *.
  destruct matches; simpl in *; eauto.
Qed.

Theorem Stable_subrelation : forall A (rel rel': A -> A -> Prop) (P: A -> Prop),
    (forall a a', rel a a' -> rel' a a') ->
    Stable P rel' ->
    Stable P rel.
Proof.
  firstorder.
Qed.

Hint Resolve disk0_wipe disk1_wipe.

Theorem TDRead0_ok : forall (i: Interface TD.API) a,
    prog_spec
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
                             d_0 a |= (fun bs => curr_val bs = v)
               | Failed => TD.disk0 state' |= missing /\
                          TD.disk1 state' |= F
               end;
           recover :=
             fun _ state' => TD.disk0 state' |= crashesTo d_0 /\
                      TD.disk1 state' |= then_wipe F;
         |})
      (Prim i (TD.Read d0 a))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  - eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - assert (TD.disk0 state'0 |= missing) by eauto.
    clear H0.
    eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
Qed.

Theorem TDRead1_ok : forall (i: Interface TD.API) a,
    prog_spec
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
                             d_1 a |= (fun bs => curr_val bs = v)
               | Failed => TD.disk0 state' |= F /\
                          TD.disk1 state' |= missing
               end;
           recover :=
             fun _ state' => TD.disk0 state' |= then_wipe F /\
                      TD.disk1 state' |= crashesTo d_1;
         |})
      (Prim i (TD.Read d1 a))
      (irec i)
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  - eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  - assert (TD.disk1 state'0 |= missing) by eauto.
    clear H5.
    eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
Qed.

(* TODO: move proofs somewhere more appropriate *)

Lemma covered_diskUpd_buffer : forall d d' a b,
    covered d d' ->
    covered (diskUpdF d a (buffer b)) (diskUpdF d' a (buffer b)).
Proof.
  intros.
  destruct H.
  eapply pointwise_rel_indomain; intros.
  autorewrite with upd; auto.

  autorewrite with upd in *.
  assert (a0 < size d') by congruence.
  specialize (pointwise_rel_holds a0).
  pose proof (@diskUpdF_inbounds _ d a (buffer b)).
  pose proof (@diskUpdF_inbounds _ d' a (buffer b)).
  is_eq a a0;
    autorewrite with upd in *; destruct matches in *;
    intuition eauto.
  repeat deex;
    repeat match goal with
           | [ H: Some _ = Some _ |- _ ] =>
             inversion H; subst; clear H
           end; simpl in *.
  eauto using collapsesTo_buffer.
Qed.

Hint Resolve covered_diskUpd_buffer.

Theorem TDWrite0_ok : forall (i: Interface TD.API) a b,
    prog_spec
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
  symmetry; eauto using sizes_eq.
Qed.

Hint Resolve covered_size_eq'.

Theorem TDDiskSize0_ok : forall (i: Interface TD.API),
    prog_spec
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
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
Qed.

Definition then_flush (F: disk -> Prop) : disk -> Prop :=
  fun d' => exists d, F d /\ pflush (flush d) d'.

Lemma maybe_holds_then_flush : forall F md d,
    md |= F ->
    md = Some d ->
    then_flush F (flush d).
Proof.
  unfold then_flush.
  intros; subst; simpl in *.
  exists d; intuition eauto.
  reflexivity.
Qed.

Hint Resolve maybe_holds_then_flush.

Lemma stable_then_flush_pflush : forall F,
    Stable (then_flush F) pflush.
Proof.
  unfold Stable, then_flush; intros.
  repeat deex.
  exists d; intuition.
  etransitivity; eauto.
Qed.

Hint Resolve stable_then_flush_pflush.

Lemma pflush_blockstate_uncached : forall (bs bs': blockstate),
    cache_val bs = None ->
    pflush_blockstate bs bs' ->
    bs = bs'.
Proof.
  inversion 2; subst; eauto.
  congruence.
Qed.

Lemma wipeBlockstate_cacheval_none : forall bs,
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
  exists d1; intuition.
  destruct H0, H1.
  eapply pointwise_rel_indomain; intros.
  etransitivity; eauto.
  simpl in *.
  specialize (pointwise_rel_holds a).
  specialize (pointwise_rel_holds0 a).
  destruct matches in *; eauto; try contradiction;
    repeat match goal with
           | [ H: pflush_blockstate _ _ |- _ ] =>
             eapply pflush_blockstate_uncached in H;
               eauto; subst
           end.
  unfold wipeBlockstate in *; simpl in *; constructor.
  destruct b1; simpl in *; subst.
  unfold wipeBlockstate in *; simpl in *; constructor.
Qed.

Hint Resolve then_wipe_then_flush.

Theorem TDSync0_ok : forall (i: Interface TD.API),
    prog_spec
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
      (refinement i).
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
    prog_spec
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
      (refinement i).
Proof.
  prim.
  destruct matches in *; cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  eapply disks_rel_stable' in H1; (safe_intuition eauto); cleanup.
  right; intuition.
  eapply pred_weaken; eauto.
  eapply pred_weaken; eauto.
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
