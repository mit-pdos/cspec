Require Import Bytes.
Require Export SepLogic.Mem.

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
           diskMem : mem addr block;
           diskMem_domain: sized_domain diskMem size; }.

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

Hint Rewrite diskUpd_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_size : upd.
Hint Rewrite diskUpd_neq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_none using (solve [ auto ]) : upd.
