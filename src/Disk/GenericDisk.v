Require Import Automation.
Require Import Omega.
Require Import RelationClasses.

Require Export Disk.Sectors.
Require Import SepLogic.Mem.Def SepLogic.Mem.Upd SepLogic.Mem.Sized.

Record diskOf T :=
  mkDisk { size: nat;
           (* The :> makes [diskMem] a coercion, allowing disks to be used in a
           few contexts where memories are expected (for example, in separation
           logic judgements). *)
           diskMem :> mem addr T;
           diskMem_domain: sized_domain diskMem size; }.

(* this coercion allows disks to be directly accessed with a function
application: [d a] will implicitly call [disk_get d a] due to the coercion,
which is [(diskMem d) a]. *)
Definition disk_get {T} (d:diskOf T) : addr -> option T := diskMem d.
Coercion disk_get : diskOf >-> Funclass.

Arguments mkDisk {T} size diskMem diskMem_domain.

Definition empty_disk {T} : diskOf T :=
  mkDisk 0 empty_mem (sized_domain_empty _).

Section GenericDisks.

  Variable (T:Type).

  Implicit Type (d:diskOf T).
  Implicit Type (b: T).

  Lemma disk_inbounds_not_none : forall a d,
      a < size d ->
      d a = None ->
      False.
  Proof.
    intros.
    pose proof (diskMem_domain d a).
    destruct matches in *; repeat deex.
    unfold disk_get in *; congruence.
  Qed.

  Lemma disk_none_oob : forall a d,
      d a = None ->
      ~a < size d.
  Proof.
    intros.
    destruct (lt_dec a (size d)); eauto.
    exfalso; eapply disk_inbounds_not_none; eauto.
  Qed.

  Definition diskUpd d (a: addr) b : diskOf T.
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

  Lemma disk_oob_eq : forall d a,
      ~a < size d ->
      d a = None.
  Proof.
    intros.
    unfold diskUpd.
    pose proof (diskMem_domain d a).
    destruct (lt_dec a (size d)); try contradiction; auto.
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

  Definition diskUpdF d (a: addr) (f: T -> T) : diskOf T.
  Proof.
    destruct (lt_dec a (size d)).
    - destruct (d a).
      refine (mkDisk (size d) (upd d a (f t)) _).
      apply sized_domain_upd_lt; auto.
      exact (diskMem_domain d).
      exact d. (* impossible, a is in bounds *)
    - exact d.
  Defined.

  Theorem diskUpdF_size_eq : forall d a f,
      size (diskUpdF d a f) = size d.
  Proof.
    unfold diskUpdF; intros.
    destruct matches; auto.
  Qed.

  Theorem diskUpdF_neq : forall d a f a',
      a <> a' ->
      diskUpdF d a f a' = d a'.
  Proof.
    unfold diskUpdF; intros.
    destruct matches; simpl; eauto.
    autorewrite with upd; auto.
  Qed.

  Theorem diskUpdF_oob : forall d a f,
      ~a < size d ->
      diskUpdF d a f = d.
  Proof.
    unfold diskUpdF; intros.
    destruct matches; simpl; eauto.
  Qed.

  Theorem diskUpdF_none : forall d a f,
      d a = None ->
      diskUpdF d a f = d.
  Proof.
    unfold diskUpdF; intros.
    destruct matches; simpl; eauto.
  Qed.

  Theorem diskUpdF_inbounds : forall d a f,
      a < size d ->
      exists v, d a = Some v /\
           diskUpdF d a f a = Some (f v).
  Proof.
    unfold diskUpdF; intros.
    pose proof (diskMem_domain d a).
    destruct matches; simpl; autorewrite with upd; eauto.
    repeat deex; unfold disk_get in *; congruence.
  Qed.

  Theorem diskUpdF_eq : forall d a f v,
      d a = Some v ->
      diskUpdF d a f a = Some (f v).
  Proof.
    unfold diskUpdF; intros.
    pose proof (diskMem_domain d a).
    destruct matches; simpl; autorewrite with upd; eauto.
    repeat deex; unfold disk_get in *; congruence.
  Qed.

  (**
   * disks are actually equal when their memories are equal;
   * besides being useful in practice, this to some extent
   * justifies the diskMem coercion, since disks are uniquely
   * determined by their memories, subject to the sized_domain
   * proofs.
   *)
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

  Theorem diskUpd_same : forall d a b,
      d a = Some b ->
      diskUpd d a b = d.
  Proof.
    intros.
    apply diskMem_ext_eq.
    extensionality a'.
    is_eq a a'; autorewrite with upd; auto.
    erewrite diskUpd_eq_some; eauto.
    rewrite diskUpd_neq by auto; auto.
  Qed.

  Lemma diskUpd_oob_noop : forall d a b,
      ~a < size d ->
      diskUpd d a b = d.
  Proof.
    intros.
    unfold diskUpd.
    pose proof (diskMem_domain d a).
    destruct (lt_dec a (size d)); try contradiction; simpl; eauto.
  Qed.

  (**
   * Support for shrinking a disk by one address.
   *)
  Definition shrink d : diskOf T.
    case_eq (size d); intros.
    - exact d.
    - refine (mkDisk n (delete (diskMem d) n) _).
      eapply sized_domain_delete_last; eauto.
      exact (diskMem_domain d).
  Defined.

  Lemma shrink_size : forall d,
      size d <> 0 ->
      size (shrink d) = size d - 1.
  Proof.
    intros.
    case_eq (size d); intros; try congruence.
    unfold shrink.
    generalize (diskMem_domain d).
    rewrite H0.
    intros; simpl; omega.
  Qed.

  Lemma shrink_preserves : forall d a,
      a <> size (shrink d) ->
      (shrink d) a = d a.
  Proof.
    intros.
    case_eq (size d); intros.
    - unfold shrink; generalize (diskMem_domain d).
      rewrite H0; auto.
    - unfold shrink; generalize (diskMem_domain d).
      rewrite H0; intros.
      simpl.
      rewrite delete_neq; auto.
      rewrite shrink_size in H by omega.
      omega.
  Qed.

End GenericDisks.

Hint Rewrite diskUpd_eq using (solve [ auto ]) : upd.
Hint Rewrite disk_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_size : upd.
Hint Rewrite diskUpd_neq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_none using (solve [ auto ]) : upd.

Hint Rewrite diskUpdF_size_eq : upd.
Hint Rewrite diskUpdF_oob using (solve [ auto ]) : upd.
Hint Rewrite diskUpdF_none using (solve [ auto ]) : upd.
Hint Rewrite diskUpdF_neq using (solve [ auto ]) : upd.

Hint Rewrite diskUpd_same using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_noop using (solve [ auto ]) : upd.

Hint Rewrite shrink_size using (solve [ auto ]) : upd.
Hint Rewrite shrink_preserves using (solve [ auto ]) : upd.

Lemma same_size_disks_not_different : forall T T' (d: diskOf T) (d': diskOf T') a v,
    size d = size d' ->
    d a = Some v ->
    d' a = None ->
    False.
Proof.
  intros.
  pose proof (diskMem_domain d' a).
  destruct (lt_dec a (size d')).
  repeat deex; unfold disk_get in *; congruence.
  pose proof (diskMem_domain d a).
  destruct (lt_dec a (size d)); unfold disk_get in *; congruence.
Qed.

Record pointwise_prop T (P: T -> Prop) (d: diskOf T) : Prop :=
  { pointwise_prop_holds :
      forall a, match d a with
           | Some bs => P bs
           | None => True
           end; }.

(* expressed for nice inversion *)
Record pointwise_rel T T' (rel: T -> T' -> Prop) (d: diskOf T) (d': diskOf T') : Prop :=
  { pointwise_sizes_eq: size d = size d';
    pointwise_rel_holds: forall a,
        match d a, d' a with
        | Some bs, Some bs' => rel bs bs'
        | None, None => True
        | _, _ => False
        end; }.

Ltac pointwise_at a :=
  repeat match goal with
         | [ H: pointwise_rel _ _ _ |- _ ] =>
           apply pointwise_rel_holds with (a:=a) in H
         end.

Ltac pointwise :=
  match goal with
  | [ |- pointwise_rel _ _ _ ] =>
    econstructor;
    [ repeat match goal with
             | [ H: pointwise_rel _ _ _ |- _ ] =>
               apply pointwise_sizes_eq in H
             end; simpl in *; try congruence |
      let a := fresh "a" in
      intro a; pointwise_at a;
      simpl in *;
      destruct matches in *; eauto; try contradiction ]
  end.

Instance pointwise_rel_preorder {T} {rel: T -> T -> Prop} {po:PreOrder rel} :
  PreOrder (pointwise_rel rel).
Proof.
  econstructor; hnf; intros.
  - pointwise.
    reflexivity.
  - pointwise.
    etransitivity; eauto.
Qed.

Theorem pointwise_rel_weaken : forall T T' (rel rel': T -> T' -> Prop) d d',
    pointwise_rel rel d d' ->
    (forall x y, rel x y -> rel' x y) ->
    pointwise_rel rel' d d'.
Proof.
  intros.
  pointwise.
Qed.

Definition mapDisk {T T'} (f: T -> T') (d:diskOf T) : diskOf T'.
Proof.
  refine {| size := size d;
            diskMem := fun a =>
                         match d a with
                         | Some v => Some (f v)
                         | None => None
                         end; |}.
  apply sized_domain_pointwise.
  apply diskMem_domain.
Defined.
