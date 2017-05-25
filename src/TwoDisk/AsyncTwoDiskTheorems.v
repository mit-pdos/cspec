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
