Require Import Automation.
Require Import Omega.
Require Import RelationClasses.
Require Import List.

Require Export Sectors.


Definition disk := list block.

(* this coercion allows disks to be directly accessed with a function
application: [d a] will implicitly call [nth_error d a] due to the coercion,
which is [(nth_error d) a]. *)
Coercion nth_error : list >-> Funclass.

Definition size (d : disk) : nat := length d.

Definition empty_disk : disk := nil.

Section GenericDisks.

  Implicit Type (d: disk).
  Implicit Type (b: block).

  Lemma disk_inbounds_not_none : forall a d,
      a < size d ->
      d a = None ->
      False.
  Proof.
    unfold size.
    intros.
    apply nth_error_None in H0.
    omega.
  Qed.

  Lemma disk_inbounds_exists : forall a d,
      a < size d ->
      exists b,
      d a = Some b.
  Proof.
    unfold size.
    intros.
    case_eq (d a); intros; eauto.
    apply nth_error_None in H0.
    omega.
  Qed.

  Lemma disk_none_oob : forall a d,
      d a = None ->
      ~a < size d.
  Proof.
    intros.
    destruct (lt_dec a (size d)); eauto.
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
      d a = Some b0 ->
      (diskUpd d a b) a = Some b.
  Proof.
    induction d; simpl; eauto.
    - destruct a; simpl; intros; congruence.
    - destruct a0; simpl; intros; eauto.
  Qed.

  Lemma diskUpd_eq : forall d a b,
      a < size d ->
      diskUpd d a b a = Some b.
  Proof.
    unfold size.
    induction d; simpl; intros.
    - omega.
    - destruct a0; simpl; intros; eauto.
      eapply IHd.
      omega.
  Qed.

  Lemma disk_oob_eq : forall d a,
      ~a < size d ->
      d a = None.
  Proof.
    unfold size.
    induction d; simpl; intros.
    - induction a; eauto.
    - destruct a0; simpl.
      + omega.
      + eapply IHd. omega.
  Qed.

  Lemma diskUpd_oob_eq : forall d a b,
      ~a < size d ->
      diskUpd d a b a = None.
  Proof.
    unfold size.
    induction d; simpl; intros.
    - induction a; eauto.
    - destruct a0; simpl.
      + omega.
      + eapply IHd. omega.
  Qed.

  Lemma diskUpd_neq : forall d a b a',
      a <> a' ->
      diskUpd d a b a' = d a'.
  Proof.
    induction d; simpl; intros; auto.
    destruct a0; simpl.
    - destruct a'; simpl; try omega; auto.
    - destruct a'; simpl; auto.
  Qed.

  Lemma diskUpd_size : forall d a b,
      size (diskUpd d a b) = size d.
  Proof.
    induction d; simpl; eauto.
    destruct a0; simpl; intros; eauto.
  Qed.

  Lemma diskUpd_none : forall d a b,
      d a = None ->
      diskUpd d a b = d.
  Proof.
    induction d; simpl; intros; auto.
    destruct a0; simpl in *; try congruence.
    rewrite IHd; eauto.
  Qed.

  Theorem disk_ext_eq : forall d d',
      (forall a, d a = d' a) ->
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
      d a = Some b ->
      diskUpd d a b = d.
  Proof.
    induction d; simpl; intros; auto.
    destruct a0; simpl in *.
    - congruence.
    - rewrite IHd; eauto.
  Qed.

  Lemma diskUpd_oob_noop : forall d a b,
      ~a < size d ->
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
      size d <> 0 ->
      size (shrink d) = size d - 1.
  Proof.
    unfold size, shrink; intros.
    rewrite firstn_length.
    rewrite min_l; omega.
  Qed.

  Lemma shrink_preserves : forall d a,
      a <> size (shrink d) ->
      (shrink d) a = d a.
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
