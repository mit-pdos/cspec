Require Import Automation.

Require Export Disk.Sectors.
Require Export SepLogic.Mem.

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

End GenericDisks.

Hint Rewrite diskUpd_eq using (solve [ auto ]) : upd.
Hint Rewrite disk_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_eq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_size : upd.
Hint Rewrite diskUpd_neq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_none using (solve [ auto ]) : upd.

Hint Rewrite diskUpdF_size_eq : upd.
Hint Rewrite diskUpdF_oob using (solve [ auto ]) : upd.
Hint Rewrite diskUpdF_neq using (solve [ auto ]) : upd.

Hint Rewrite diskUpd_same using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_noop using (solve [ auto ]) : upd.

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

(* expressed for nice inversion *)
Record pointwise_rel T T' (rel: T -> T' -> Prop) (d: diskOf T) (d': diskOf T') : Prop :=
  { sizes_eq: size d = size d';
    pointwise_rel_holds: forall a,
        match d a, d' a with
        | Some bs, Some bs' => rel bs bs'
        | None, None => ~a < size d
        | _, _ => False
        end; }.

Local Hint Resolve disk_inbounds_not_none.

(* convenience to prove pointwise_rel with minimal proof *)
Theorem pointwise_rel_indomain : forall T T' (rel: T -> T' -> Prop) d d',
    size d = size d' ->
    (forall a, a < size d ->
          match d a, d' a with
          | Some bs, Some bs' => rel bs bs'
          | _, _ => True
          end) ->
    pointwise_rel rel d d'.
Proof.
  intros.
  econstructor; intros; eauto.
  specialize (H0 a).
  destruct (lt_dec a (size d)); intuition eauto.
  assert (a < size d') by congruence.
  destruct matches; eauto.

  assert (~a < size d') by congruence.
  autorewrite with upd; auto.
Qed.

Theorem pointwise_rel_trans : forall T (rel: T -> T -> Prop),
    forall (Htrans: forall x y z, rel x y -> rel y z -> rel x z),
    forall d d' d'',
      pointwise_rel rel d d' ->
      pointwise_rel rel d' d'' ->
      pointwise_rel rel d d''.
Proof.
  intros.
  destruct H.
  destruct H0.
  eapply pointwise_rel_indomain; intros.
  congruence.
  specialize (pointwise_rel_holds0 a).
  specialize (pointwise_rel_holds1 a).
  destruct matches in *; eauto; try contradiction.
Qed.

Definition rel_compose T T' T'' (rel: T -> T' -> Prop)
           (rel': T' -> T'' -> Prop) :
  T -> T'' -> Prop :=
  fun a a'' => exists a', rel a a' /\ rel' a' a''.

Theorem pointwise_rel_trans' : forall T T' T''
                                 (rel: T -> T' -> Prop)
                                 (rel': T' -> T'' -> Prop),
    forall d d' d'',
      pointwise_rel rel d d' ->
      pointwise_rel rel' d' d'' ->
      pointwise_rel (rel_compose rel rel') d d''.
Proof.
  intros.
  destruct H.
  destruct H0.
  eapply pointwise_rel_indomain; intros.
  congruence.
  specialize (pointwise_rel_holds0 a).
  specialize (pointwise_rel_holds1 a).
  destruct matches in *; eauto; try contradiction.
  unfold rel_compose; eauto.
Qed.

Instance pointwise_rel_preorder {T} {rel: T -> T -> Prop} {po:PreOrder rel} :
  PreOrder (pointwise_rel rel).
Proof.
  econstructor; hnf; intros.
  - eapply pointwise_rel_indomain; intros; eauto.
    destruct matches; eauto.
    reflexivity.
  - eapply pointwise_rel_trans; eauto.
    intros.
    etransitivity; eauto.
Qed.

Theorem pointwise_rel_weaken : forall T T' (rel rel': T -> T' -> Prop) d d',
    pointwise_rel rel d d' ->
    (forall x y, rel x y -> rel' x y) ->
    pointwise_rel rel' d d'.
Proof.
  intros.
  destruct H.
  eapply pointwise_rel_indomain; intros; eauto.
  specialize (pointwise_rel_holds0 a).
  destruct matches in *; eauto; try contradiction.
Qed.

Definition mapDisk {T T'} (d:diskOf T) (f: T -> T') : diskOf T'.
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

Theorem pointwise_rel_mapDisk : forall T T' (d: diskOf T) (f: T -> T'),
    pointwise_rel (fun a a' => a' = f a) d (mapDisk d f).
Proof.
  intros.
  eapply pointwise_rel_indomain; intros; eauto.
  simpl; destruct matches.
Qed.
