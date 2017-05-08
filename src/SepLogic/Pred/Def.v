Require Import Automation.
Require Import Setoid Classes.Morphisms.
Require Import SepLogic.Mem.Def.

(* [pred A V] is a predicate over [mem A V]; we wrap it in a record to make
judgements explicit rather than mere function applications.

 However, using [pred_prop] to construct a judgement would be tedious; when
 shorthand is desired, we use :> to supply a coercion from pred to Funclass, so
 that predicates can be directly applied to memories to produce propositions.
*)
Record pred A V :=
  mkPred { pred_prop : mem A V -> Prop }.

Section Predicates.

  Context {A V:Type}.
  Implicit Types p q:pred A V.

  (* for shorthand while writing basic lemmas, we allow predicates to be applied
  directly to memories via this coercion (due to the Local modifier it will be
  removed at the end of the section) *)
  Local Coercion pred_prop : pred >-> Funclass.

  (** [lift P] (denoted [|P|]) states that m is empty, and that the proposition
  P holds. *)
  Definition lift (P:Prop) : pred A V :=
    mkPred (fun m => P /\ m = empty_mem).
  Definition emp := lift True.
  Definition exis X (P: X -> pred A V) :=
    mkPred (fun m => exists x, pred_prop (P x) m).

  (** [ptsto a v] (denoted a |-> v) states that address [a] maps to [v], and no
  other addresses map to anything. *)
  Definition ptsto (a:A) (v:V) : pred A V :=
    mkPred (fun m => m a = Some v /\
                  forall a', a <> a' -> m a' = None).

  (** The core connective of separation logic, also called the separating
  conjunction. [star p q] (denoted p * q) says that the heap can be split into
  disjoint pieces which satisfy [p] and [q] respectively. *)
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

  Global Add Parametric Relation :
    (pred A V) pimpl
      reflexivity proved by pimpl_refl
      transitivity proved by pimpl_trans
        as pimpl_rel.

  Lemma peq_refl : forall p, p === p.
  Proof.
    firstorder.
  Qed.

  Lemma peq_trans : forall p q r, p === q -> q === r -> p === r.
  Proof.
    firstorder.
  Qed.

  Global Add Parametric Relation :
    (pred A V) peq
      reflexivity proved by peq_refl
      transitivity proved by peq_trans
        as peq_rel.

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

  Global Add Parametric Morphism : star
      with signature peq ==> peq ==> peq
        as star_mor.
  Proof.
    unfold peq; intuition auto using star_cancel.
  Qed.

  Global Add Parametric Morphism : star
      with signature pimpl ==> pimpl ==> pimpl
        as star_mor'.
  Proof.
    auto using star_cancel.
  Qed.

  Global Instance pimpl_peq_mor : Proper (peq ==> peq ==> iff) pimpl.
  Proof.
    hnf; intros; hnf; intros.
    unfold peq in *; safe_intuition.
    intuition eauto using pimpl_trans.
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

  Lemma pimpl_apply : forall m F F',
      pred_prop F m ->
      F ===> F' ->
      pred_prop F' m.
  Proof.
    unfold pimpl; simpl; eauto.
  Qed.

  Theorem lift_extract : forall m P,
      [|P|] m -> P.
  Proof.
    unfold lift; simpl in *; intuition.
  Qed.

  Theorem lift_star_left : forall (P: Prop) p m,
      (star [|P|] p) m ->
      P /\ p m.
  Proof.
    simpl; intros.
    repeat deex.
    rewrite mem_union_empty; eauto.
  Qed.

End Predicates.

(** * Notation magic to make separation logic easy to write in Coq. *)

Delimit Scope pred_scope with pred.

Notation "[| P |]" := (lift P) (at level 0) : pred_scope.
Notation "p * q" := (star p%pred q%pred) : pred_scope.

Notation "p === q" := (peq p%pred q%pred) (no associativity, at level 70).
Notation "p ===> q" := (pimpl p%pred q%pred) (no associativity, at level 70).

Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p%pred)) ..)) : pred_scope.

Infix "|->" := ptsto (no associativity, at level 30) : pred_scope.

Notation "m |= F" := (pred_prop F%pred m) (at level 20, F at level 50).
