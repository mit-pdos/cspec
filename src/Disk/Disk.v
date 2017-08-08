Require Import Automation.
Require Import Omega.
Require Import RelationClasses.
Require Import List.

Require Export Sectors.


Definition disk := list block.

Definition diskGet (d : disk) (a : addr) : option block :=
  nth_error d a.

Definition diskSize (d : disk) : nat := length d.

Definition empty_disk : disk := nil.

Section GenericDisks.

  Implicit Type (d: disk).
  Implicit Type (b: block).

  Lemma disk_inbounds_not_none : forall a d,
      a < diskSize d ->
      diskGet d a = None ->
      False.
  Proof.
    unfold diskSize.
    intros.
    apply nth_error_None in H0.
    omega.
  Qed.

  Lemma disk_inbounds_exists : forall a d,
      a < diskSize d ->
      exists b,
      diskGet d a = Some b.
  Proof.
    unfold diskSize.
    intros.
    case_eq (diskGet d a); intros; eauto.
    apply nth_error_None in H0.
    omega.
  Qed.

  Lemma disk_none_oob : forall a d,
      diskGet d a = None ->
      ~a < diskSize d.
  Proof.
    intros.
    destruct (lt_dec a (diskSize d)); eauto.
    exfalso; eapply disk_inbounds_not_none; eauto.
  Qed.

  Fixpoint diskUpd d (a: addr) b : disk :=
    match d with
    | nil => nil
    | db :: drest =>
      match a with
      | O => b :: drest
      | S a' => db :: diskUpd drest a' b
      end
    end.

  Lemma diskUpd_eq_some : forall d a b0 b,
      diskGet d a = Some b0 ->
      diskGet (diskUpd d a b) a = Some b.
  Proof.
    induction d; simpl; eauto.
    - destruct a; simpl; intros; congruence.
    - destruct a0; simpl; intros; eauto.
  Qed.

  Lemma diskUpd_eq : forall d a b,
      a < diskSize d ->
      diskGet (diskUpd d a b) a = Some b.
  Proof.
    unfold diskSize.
    induction d; simpl; intros.
    - omega.
    - destruct a0; simpl; intros; eauto.
      eapply IHd.
      omega.
  Qed.

  Lemma disk_oob_eq : forall d a,
      ~a < diskSize d ->
      diskGet d a = None.
  Proof.
    unfold diskSize.
    induction d; simpl; intros.
    - induction a; eauto.
    - destruct a0; simpl.
      + omega.
      + eapply IHd. omega.
  Qed.

  Lemma diskUpd_oob_eq : forall d a b,
      ~a < diskSize d ->
      diskGet (diskUpd d a b) a = None.
  Proof.
    unfold diskSize.
    induction d; simpl; intros.
    - induction a; eauto.
    - destruct a0; simpl.
      + omega.
      + eapply IHd. omega.
  Qed.

  Lemma diskUpd_neq : forall d a b a',
      a <> a' ->
      diskGet (diskUpd d a b) a' = diskGet d a'.
  Proof.
    induction d; simpl; intros; auto.
    destruct a0; simpl.
    - destruct a'; simpl; try omega; auto.
    - destruct a'; simpl; auto.
  Qed.

  Lemma diskUpd_size : forall d a b,
      diskSize (diskUpd d a b) = diskSize d.
  Proof.
    induction d; simpl; eauto.
    destruct a0; simpl; intros; eauto.
  Qed.

  Lemma diskUpd_none : forall d a b,
      diskGet d a = None ->
      diskUpd d a b = d.
  Proof.
    induction d; simpl; intros; auto.
    destruct a0; simpl in *; try congruence.
    rewrite IHd; eauto.
  Qed.

  Theorem disk_ext_eq : forall d d',
      (forall a, diskGet d a = diskGet d' a) ->
      d = d'.
  Proof.
    induction d; simpl; intros.
    - destruct d'; simpl; intros; eauto.
      specialize (H 0); simpl in *.
      congruence.
    - destruct d'; simpl; intros.
      + specialize (H 0); simpl in *.
        congruence.
      + specialize (H 0) as H'; simpl in H'.
        f_equal; try congruence.
        eapply IHd; intros.
        specialize (H (S a0)); simpl in H.
        eauto.
  Qed.

  Theorem diskUpd_same : forall d a b,
      diskGet d a = Some b ->
      diskUpd d a b = d.
  Proof.
    induction d; simpl; intros; auto.
    destruct a0; simpl in *.
    - congruence.
    - rewrite IHd; eauto.
  Qed.

  Lemma diskUpd_oob_noop : forall d a b,
      ~a < diskSize d ->
      diskUpd d a b = d.
  Proof.
    induction d; simpl; intros; auto.
    destruct a0; simpl in *.
    - omega.
    - rewrite IHd; auto; omega.
  Qed.

  (**
   * Support for shrinking a disk by one address.
   *)
  Definition shrink (d : disk) : disk :=
    firstn (length d - 1) d.

  Lemma shrink_size : forall d,
      diskSize d <> 0 ->
      diskSize (shrink d) = diskSize d - 1.
  Proof.
    unfold diskSize, shrink; intros.
    rewrite firstn_length.
    rewrite min_l; omega.
  Qed.

  Lemma shrink_preserves : forall d a,
      a <> diskSize (shrink d) ->
      diskGet (shrink d) a = diskGet d a.
  Proof.
    unfold shrink.
    induction d; simpl; intros; auto.
    destruct d; simpl in *.
    - destruct a0; try omega; simpl.
      destruct a0; auto.
    - destruct a0; simpl; auto.
      replace (length d - 0) with (length d) in * by omega.
      rewrite <- IHd; auto.
  Qed.

End GenericDisks.

Hint Rewrite diskUpd_eq using (solve [ auto ]) : upd.
Hint Rewrite disk_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_size : upd.
Hint Rewrite diskUpd_neq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_none using (solve [ auto ]) : upd.

Hint Rewrite diskUpd_same using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_noop using (solve [ auto ]) : upd.

Hint Rewrite shrink_size using (solve [ auto ]) : upd.
Hint Rewrite shrink_preserves using (solve [ auto ]) : upd.
