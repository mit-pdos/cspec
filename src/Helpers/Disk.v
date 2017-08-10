Require Import Automation.
Require Import Omega.
Require Import RelationClasses.
Require Import List.
Require Import Helpers.


(** * Disk model.

    This file defines our model of a disk.  The first thing to
    do is to define the two basic types: an address and a block.
    For us, an address [addr] is simply a [nat], and a block is
    an array of bytes (the size being the block size).
  *)

Definition addr := nat.

(** We define the block size as a separate constant, [blockbytes],
    so that we can later make it opaque.  This helps avoid Coq
    expanding out [blockbytes] into the literal constant [1024],
    which helps with performance.
  *)

Definition blockbytes := 1024.

Definition block := bytes blockbytes.
Definition block0 : block := bytes0 _.
Definition block1 : block := bytes1 _.

Theorem block0_block1_differ : block0 <> block1.
Proof.
  apply bytes_differ.
  unfold blockbytes.
  omega.
Qed.

Hint Resolve block0_block1_differ.

(** Coq v8.6 has a minor bug in the [omega] tactic, which is helpful
    in solving simple arithmetic goals.  In particular, when we have
    arithmetic expressions that involve the [addr] type, [omega] gets
    confused because it doesn't see that [addr] is simply a wrapper
    for [nat].  This works around the bug, which should eventually be
    fixed by https://github.com/coq/coq/pull/876
  *)

Local Ltac omega_orig := omega.
Ltac omega := unfold addr in *; omega_orig.

(** Mark [blockbytes] as opaque so that Coq doesn't expand it too eagerly.
  *)

Opaque blockbytes.


(** * Disk as a list of blocks.

    Now we can define our model of a disk: a list of blocks.
    A disk with zero blocks is an empty list, [nil].
  *)

Definition disk := list block.

Definition empty_disk : disk := nil.

(** We define three main operations on disks:

    - [diskGet d a] gets the contents of an address [a] in disk [d].
      It returns an [option block], which is either a block value [b]
      (represented by [Some b]), or [None] if [a] is past the end of
      the disk.

    - [diskSize] returns the size of the disk, which is just the length
      of the list representing the disk.

    - [diskUpd] writes to a disk.  Since Gallina is a functional language,
      we cannot update a disk "in-place", so instead [diskUpd] returns a
      new disk reflecting the write.  Specifically, [diskUpd d a b] returns
      a new disk with address [a] updated to block value [b], if [a] is
      in-bounds, or no changes if [a] is out-of-bounds.
  *)

Definition diskGet (d : disk) (a : addr) : option block :=
  nth_error d a.

Definition diskSize (d : disk) : nat := length d.

Fixpoint diskUpd d (a: addr) b : disk :=
  match d with
  | nil => nil
  | db :: drest =>
    match a with
    | O => b :: drest
    | S a' => db :: diskUpd drest a' b
    end
  end.

(** We also define another helper operation, [diskShrink], which takes
    a disk and drops the last block.  This will be helpful in the
    bad-block-remapping lab assignment.
  *)

Definition diskShrink (d : disk) : disk :=
  firstn (length d - 1) d.

(** Finally, we prove a variety of lemmas about the behavior of these
    disk operations.
  *)

Theorem disk_inbounds_not_none : forall a d,
    a < diskSize d ->
    diskGet d a = None ->
    False.
Proof.
  unfold diskSize.
  intros.
  apply nth_error_None in H0.
  omega.
Qed.

Theorem disk_inbounds_exists : forall a d,
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

Theorem disk_none_oob : forall a d,
    diskGet d a = None ->
    ~a < diskSize d.
Proof.
  intros.
  destruct (lt_dec a (diskSize d)); eauto.
  exfalso; eapply disk_inbounds_not_none; eauto.
Qed.

Theorem diskUpd_eq_some : forall d a b0 b,
    diskGet d a = Some b0 ->
    diskGet (diskUpd d a b) a = Some b.
Proof.
  induction d; simpl; eauto.
  - destruct a; simpl; intros; congruence.
  - destruct a0; simpl; intros; eauto.
Qed.

Theorem diskUpd_eq : forall d a b,
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

Theorem disk_oob_eq : forall d a,
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

Theorem diskUpd_oob_eq : forall d a b,
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

Theorem diskUpd_neq : forall d a b a',
    a <> a' ->
    diskGet (diskUpd d a b) a' = diskGet d a'.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl.
  - destruct a'; simpl; try omega; auto.
  - destruct a'; simpl; auto.
Qed.

Theorem diskUpd_size : forall d a b,
    diskSize (diskUpd d a b) = diskSize d.
Proof.
  induction d; simpl; eauto.
  destruct a0; simpl; intros; eauto.
Qed.

Theorem diskUpd_none : forall d a b,
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

Theorem diskUpd_twice : forall d a b b',
    diskUpd (diskUpd d a b) a b' = diskUpd d a b'.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *.
  - congruence.
  - rewrite IHd; eauto.
Qed.

Theorem diskUpd_oob_noop : forall d a b,
    ~a < diskSize d ->
    diskUpd d a b = d.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *.
  - omega.
  - rewrite IHd; auto; omega.
Qed.

Theorem diskShrink_size : forall d,
    diskSize d <> 0 ->
    diskSize (diskShrink d) = diskSize d - 1.
Proof.
  unfold diskSize, diskShrink; intros.
  rewrite firstn_length.
  rewrite min_l; omega.
Qed.

Theorem diskShrink_preserves : forall d a,
    a <> diskSize (diskShrink d) ->
    diskGet (diskShrink d) a = diskGet d a.
Proof.
  unfold diskShrink.
  induction d; simpl; intros; auto.
  destruct d; simpl in *.
  - destruct a0; try omega; simpl.
    destruct a0; auto.
  - destruct a0; simpl; auto.
    replace (length d - 0) with (length d) in * by omega.
    rewrite <- IHd; auto.
Qed.

Theorem diskShrink_diskUpd_last : forall d a b,
    a >= diskSize d - 1 ->
    diskShrink (diskUpd d a b) = diskShrink d.
Proof.
  unfold diskShrink; intros.
  destruct (eq_nat_dec a (diskSize d - 1)); subst.
  - clear H.
    rewrite diskUpd_size; unfold diskSize.
    induction d; simpl; auto.
    destruct d; simpl in *; auto.
    replace (length d - 0) with (length d) in * by omega.
    f_equal; auto.
  - rewrite diskUpd_oob_noop by omega; auto.
Qed.

Theorem diskShrink_diskUpd_notlast : forall d a b,
    a < diskSize d - 1 ->
    diskShrink (diskUpd d a b) = diskUpd (diskShrink d) a b.
Proof.
  unfold diskShrink.
  induction d; simpl; auto; intros.
  destruct a0; simpl; auto.
  - destruct d; simpl; auto.
  - destruct d; simpl in *; auto.
    replace (length d - 0) with (length d) in * by omega.
    rewrite <- IHd by omega.
    destruct a0; simpl; try rewrite diskUpd_size; unfold diskSize;
      replace (length d - 0) with (length d) by omega; auto.
Qed.

(** We combine all of the above lemmas into a hint database called "upd".
    This means that, when you type [autorewrite with upd] in some Coq proof,
    Coq will try to rewrite using all of the hints in that database.

    The [using] part of the hint tells Coq that all of the side conditions
    associated with the rewrite must be solved using the tactic specified
    in the [using] clause.  This prevents Coq from applying a rewrite rule
    if some side condition (like an address being out-of-bounds) cannot be
    immediately proven.
  *)

Hint Rewrite diskUpd_eq using (solve [ auto ]) : upd.
Hint Rewrite disk_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_size : upd.
Hint Rewrite diskUpd_neq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_none using (solve [ auto ]) : upd.

Hint Rewrite diskUpd_same using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_noop using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_twice : upd.

Hint Rewrite diskShrink_size using (solve [ auto || omega ]) : upd.
Hint Rewrite diskShrink_preserves using (solve [ auto || omega ]) : upd.
Hint Rewrite diskShrink_diskUpd_last using (solve [ auto || omega ]) : upd.
Hint Rewrite diskShrink_diskUpd_notlast using (solve [ auto || omega ]) : upd.
