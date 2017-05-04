Require Import Automation.

Require Import Bytes.
Require Export SepLogic.Mem.
Require Import SepLogic.Pred.

Definition addr := nat.

(* We introduce this definition to make the large constant opaque, for
performance reasons. *)
Definition fourkilobytes := 4096.
Opaque fourkilobytes.
Definition block := bytes fourkilobytes.
Definition block0 : block := bytes0 fourkilobytes.
Opaque block.

Record disk :=
  mkDisk { size: nat;
           (* The :> makes [diskMem] a coercion, allowing disks to be used in a
           few contexts where memories are expected (for example, in separation
           logic judgements). *)
           diskMem :> mem addr block;
           diskMem_domain: sized_domain diskMem size; }.

Definition dpred := pred addr block.

(* this coercion allows disks to be directly accessed with a function
application: [d a] will implicitly call [disk_get d a] due to the coercion,
which is [(diskMem d) a]. *)
Definition disk_get (d:disk) : addr -> option block := diskMem d.
Coercion disk_get : disk >-> Funclass.

Arguments mkDisk size diskMem diskMem_domain : clear implicits.

Definition empty_disk : disk := mkDisk 0 empty_mem (sized_domain_empty _).

Implicit Type (d:disk).

Definition diskUpd d (a: addr) (b: block) : disk.
Proof.
  destruct (lt_dec a (size d)).
  - refine (mkDisk (size d) (upd d a b) _).
    apply sized_domain_upd_lt; auto.
    exact (diskMem_domain d).
  - exact d.
Defined.

Lemma diskUpd_eq_some : forall d a b0 b,
    disk_get d a = Some b0 ->
    disk_get (diskUpd d a b) a = Some b.
Proof.
  intros.
  pose proof (diskMem_domain d a).
  unfold diskUpd.
  destruct (lt_dec a (size d)); try contradiction; simpl.
  autorewrite with upd; auto.
  unfold disk_get in *.
  congruence.
Qed.

Lemma diskUpd_eq : forall d a b,
    a < size d ->
    diskUpd d a b a = Some b.
Proof.
  intros.
  unfold diskUpd.
  destruct (lt_dec a (size d)); try contradiction; simpl.
  autorewrite with upd; auto.
Qed.

Lemma diskUpd_oob_eq : forall d a b,
    ~a < size d ->
    diskUpd d a b a = None.
Proof.
  intros.
  unfold diskUpd.
  pose proof (diskMem_domain d a).
  destruct (lt_dec a (size d)); try contradiction; simpl; eauto.
Qed.

Lemma diskUpd_neq : forall d a b a',
    a <> a' ->
    diskUpd d a b a' = d a'.
Proof.
  intros.
  unfold diskUpd.
  destruct (lt_dec a (size d)); simpl;
    autorewrite with upd; auto.
Qed.

Lemma diskUpd_size : forall d a b,
    size (diskUpd d a b) = size d.
Proof.
  unfold diskUpd; intros.
  destruct (lt_dec a (size d)); eauto.
Qed.

Lemma diskUpd_none : forall d a b,
    d a = None ->
    diskUpd d a b = d.
Proof.
  unfold diskUpd; intros.
  pose proof (diskMem_domain d a).
  destruct (lt_dec a (size d)); eauto.
  destruct H0; unfold disk_get in *; try congruence.
Qed.

Lemma ptsto_diskUpd : forall d a b0 b F,
    d |= F * a |-> b0 ->
    diskUpd d a b |= F * a |-> b.
Proof.
  intros.
  pose proof (ptsto_valid H).
  pose proof (diskMem_domain d a).
  unfold diskUpd.
  destruct matches.
  cbn [diskMem].
  eapply ptsto_upd; eauto.
Qed.

Lemma diskUpd_diskMem_commute : forall d a b0 b,
    d a = Some b0 ->
    diskMem (diskUpd d a b) = upd (diskMem d) a b.
Proof.
  intros.
  extensionality a'.
  is_eq a a'; autorewrite with upd; eauto.
  erewrite diskUpd_eq_some; eauto.
  rewrite diskUpd_neq; auto.
Qed.

Hint Rewrite diskUpd_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_size : upd.
Hint Rewrite diskUpd_neq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_none using (solve [ auto ]) : upd.

(* disks are actually equal when their memories are equal; besides being useful
 in practice, this to some extent justifies the diskMem coercion, since disks
 are uniquely determined by their memories, subject to the sized_domain
 proofs. *)
Theorem diskMem_ext_eq : forall d d',
    diskMem d = diskMem d' ->
    d = d'.
Proof.
  intros.
  destruct d, d'; simpl in *; subst.
  pose proof (sized_domain_unique_sz diskMem_domain0 diskMem_domain1); subst.
  f_equal.
  apply ProofIrrelevance.proof_irrelevance.
Qed.
