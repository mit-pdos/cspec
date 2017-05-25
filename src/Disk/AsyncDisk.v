Require Import Automation.

Require Export Disk.GenericDisk.

(* we only import List for the [In] predicate *)
Require List.
Require Import Nonempty.
Require Import Sized.

Definition blockset := nonempty block.

Definition latest (bs:blockset) : block := head bs.
Definition buffer (b: block) (bs:blockset) : blockset := prepend b bs.

(* TODO: we may want to use only (current value, on-platter value) for the
representation, and use disksets or diskset-like things only for predicates *)

Definition disk := diskOf blockset.

Inductive covers : blockset -> blockset -> Prop :=
| is_cover : forall b bs bs',
    (forall b', List.In b' bs' ->
           b' = b \/ List.In b' bs) ->
    covers (necons b bs) (necons b bs').

Instance covers_preorder : PreOrder covers.
Proof.
  econstructor; hnf; intros.
  - destruct x.
    eapply is_cover; intros; eauto.
  - inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    eapply is_cover; intros.
    specialize (H4 _ ltac:(eauto)).
    intuition eauto.
Qed.

Record covered (d:disk) (d':disk) : Prop :=
  is_covered
    { covered_size_eq: size d = size d';
      covers_pointwise: forall a bs bs',
          d a = Some bs ->
          d' a = Some bs' ->
          covers bs bs'; }.

Instance covered_preorder : PreOrder covered.
Proof.
  econstructor; hnf; intros.
  - econstructor; intros; eauto.
    assert (bs = bs') by congruence; subst.
    reflexivity.
  - econstructor; intros; eauto.
    + destruct H, H0; congruence.
    + pose proof (covers_pointwise H a).
      pose proof (covers_pointwise H0 a).
      destruct (y a) eqn:?.
      specialize (H3 _ _ ltac:(eauto) ltac:(eauto)).
      specialize (H4 _ _ ltac:(eauto) ltac:(eauto)).
      etransitivity; eauto.
      exfalso.
      eauto using same_size_disks_not_different,
      covered_size_eq.
Qed.

Definition flush (d:disk) : disk.
  refine {| size := size d;
            diskMem := fun a =>
                         match d a with
                         | Some bs => Some (keepFirst bs)
                         | None => None
                         end; |}.
  apply sized_domain_pointwise.
  apply diskMem_domain.
Defined.

Theorem flush_size_eq : forall d,
    size (flush d) = size d.
Proof.
  auto.
Qed.

(* discard write buffers (wipe in-memory state) *)
Definition oldest (d:disk) : disk.
  refine {| size := size d;
            diskMem := fun a =>
                         match d a with
                         | Some bs => Some (keepLast bs)
                         | None => None
                         end; |}.
  apply sized_domain_pointwise.
  apply diskMem_domain.
Defined.

Theorem oldest_size_eq : forall d,
    size (oldest d) = size d.
Proof.
  auto.
Qed.

(* partial flush at each address; expressed for convenient inversion *)
Inductive pflushed : disk -> disk -> Prop :=
| is_pflushed : forall d d',
    size d = size d' ->
    (forall a, match d a, d' a with
          | Some bs, Some bs' => covers bs bs'
          | None, None => ~a < size d
          | _, _ => False
          end) ->
    pflushed d d'.

Local Hint Resolve disk_inbounds_not_none.

Theorem pflushed_indomain : forall d d',
    size d = size d' ->
    (forall a, a < size d ->
          match d a, d' a with
          | Some bs, Some bs' => covers bs bs'
          | _, _ => True
          end) ->
    pflushed d d'.
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
