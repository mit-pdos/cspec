Require Import Automation.
Require Import Setoid Classes.Morphisms.
Require Import SepLogic.Mem.Def.

Record pred A V :=
  mkPred { pred_prop :> mem A V -> Prop }.

Section Predicates.

  Context {A V:Type}.
  Implicit Types p q:pred A V.

  Definition lift (P:Prop) : pred A V :=
    mkPred (fun m => P /\ m = empty_mem).
  Definition emp := lift True.
  Definition exis X (P: X -> pred A V) :=
    mkPred (fun m => exists x, P x m).

  Definition ptsto (a:A) (v:V) : pred A V :=
    mkPred (fun m => m a = Some v /\
                  forall a', a <> a' -> m a' = None).

  Definition star p q : pred A V :=
    mkPred (fun m => exists m1 m2, p m1 /\
                           q m2 /\
                           mem_disjoint m1 m2 /\
                           m = mem_union m1 m2).

  Definition pimpl p q :=
    forall m, p m -> q m.

  Definition peq p q :=
    pimpl p q /\ pimpl q p.

  Notation "[| P |]" := (lift P) (at level 0).
  Infix "*" := star.

  Infix "===" := peq (no associativity, at level 70).
  Infix "===>" := pimpl (no associativity, at level 70).

  Lemma pimpl_refl : forall p, p ===> p.
  Proof.
    firstorder.
  Qed.

  Lemma pimpl_trans : forall p q r, p ===> q -> q ===> r -> p ===> r.
  Proof.
    firstorder.
  Qed.

  Add Parametric Relation :
    (pred A V) pimpl
      reflexivity proved by pimpl_refl
      transitivity proved by pimpl_trans
        as pimpl_rel.

  Hint Resolve mem_disjoint_comm.
  Hint Resolve mem_union_comm.

  Hint Resolve mem_disjoint_from_union_1.
  Hint Resolve mem_disjoint_from_union_2.
  Hint Resolve mem_disjoint_both_to_union.
  Hint Resolve mem_union_assoc.

  Theorem star_comm : forall p q,
      p * q === q * p.
  Proof.
    assert (forall p q, p * q ===> q * p).
    unfold star, pimpl; simpl; intuition.
    repeat deex.
    descend; intuition eauto.

    unfold peq; intuition.
  Qed.

  Theorem star_cancel : forall p1 p2 q1 q2,
      p1 ===> p2 ->
      q1 ===> q2 ->
      p1 * q1 ===> p2 * q2.
  Proof.
    unfold star, pimpl; simpl; intros.
    repeat deex.
    descend; intuition eauto.
  Qed.

  Add Parametric Morphism : star
      with signature peq ==> peq ==> peq
        as star_mor.
  Proof.
    unfold peq; intuition auto using star_cancel.
  Qed.

  Add Parametric Morphism : star
      with signature pimpl ==> pimpl ==> pimpl
        as star_mor'.
  Proof.
    auto using star_cancel.
  Qed.

  Theorem star_assoc : forall p q r,
      p * (q * r) === (p * q) * r.
  Proof.
    unfold star, peq, pimpl; simpl; intuition.
    - repeat deex.
      exists (mem_union m1 m0), m3; intuition eauto.
      descend; intuition eauto.
      eapply mem_disjoint_comm; eauto.
      rewrite mem_union_assoc; eauto.
    - repeat deex.
      exists m0, (mem_union m3 m2); intuition eauto.
      descend; intuition eauto.
  Qed.

  Theorem lift_extract : forall m P,
      pred_prop [|P|] m -> P.
  Proof.
    unfold lift; simpl in *; intuition.
  Qed.

End Predicates.

Notation "[| P |]" := (lift P) (at level 0) : pred_scope.
Infix "*" := star : pred_scope.

Infix "===" := peq (no associativity, at level 70) : pred_scope.
Infix "===>" := pimpl (no associativity, at level 70) : pred_scope.

Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : pred_scope.

Infix "|->" := ptsto (no associativity, at level 30) : pred_scope.

Add Printing Coercion pred_prop.
Delimit Scope pred_scope with pred.
Notation "m |= F" := (pred_prop F%pred m) (at level 20, F at level 50).
