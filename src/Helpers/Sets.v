Require Import List.
Require Import Maps.
Require Import Ordering.

Set Implicit Arguments.

Theorem Forall_impl : forall A (P P': A -> Prop) l,
    (forall x, P x -> P' x) ->
    Forall P l ->
    Forall P' l.
Proof.
  induction l; simpl; intuition eauto.
  inversion H0; eauto.
Qed.

Module FSet.

  Section Sets.

    Variable A:Type.
    Context {Acmp:Ordering A}.

    Definition t := FMap.t A unit.
    Definition empty : t := FMap.empty.

    Definition elements (s:t) : list A :=
      FMap.keys s.

    Definition In x (s:t) :=
      FMap.In x s.

    Hint Unfold empty In : set.

    Ltac unfold_set :=
      intros;
      autounfold with set in *.

    Theorem _in_mapsto : forall x u s,
        FMap.MapsTo x u s ->
        In x s.
    Proof.
      unfold_set.
      apply FMap.mapsto_in in H; auto.
    Qed.

    Theorem _in_mapsto' : forall x s,
        FMap.In x s ->
        FMap.MapsTo x tt s.
    Proof.
      unfold_set.
      apply FMap.in_mapsto_exists in H.
      destruct H as [[] ?]; auto.
    Qed.

    Definition For_all (P:A -> Prop) (s:t) :=
      FMap.For_all (fun '(k, _) => P k) s.

    Hint Unfold For_all : set.

    Theorem empty_Forall : forall P,
        For_all P empty.
    Proof.
      unfold_set.
      apply FMap.empty_Forall.
    Qed.

     Theorem For_all_in (P:A -> Prop) (s:t) :
      For_all P s ->
      forall x, In x s -> P x.
    Proof.
      unfold_set.
      eapply FMap.For_all_in in H; eauto.
      apply _in_mapsto'; auto.
    Qed.

    Theorem not_in_forall : forall x s,
        ~In x s ->
        For_all (fun y => x <> y) s.
    Proof.
      unfold_set.
      eapply FMap.not_in_forall in H.
      eapply Forall_impl; eauto.
      intros.
      destruct x0; simpl in *; auto.
    Qed.

    Definition In_dec x s : {In x s} + {~In x s}.
      apply FMap.In_dec.
    Defined.

    Definition add (x:A) (s:t) : t :=
      FMap.add x tt s.

    Theorem add_forall : forall x P s,
        For_all P s ->
        P x ->
        For_all P (add x s).
    Proof.
      unfold_set.
      eapply FMap.add_forall; eauto.
    Qed.

    Theorem add_forall' : forall x P s,
        For_all P (add x s) ->
        For_all P s.
    Proof.
      unfold_set.
      destruct (FMap.In_dec x s).
      apply _in_mapsto' in i.
      assert (FMap.In x (add x s)).
      eapply FMap.add_in.
      apply _in_mapsto' in H0.
      assert (P x) by (eapply FMap.For_all_in in H; eauto).
      eapply FMap.add_forall'_in; eauto.
      eapply FMap.add_forall'; eauto.
    Qed.

    Theorem add_in : forall x s,
        In x (add x s).
    Proof.
      unfold_set.
      apply FMap.add_in.
    Qed.

    Theorem add_in' : forall x s y,
        In x (add y s) ->
        x = y \/ In x s.
    Proof.
      unfold_set.
      apply FMap.add_in' in H; auto.
    Qed.

    Theorem add_incr : forall x s y,
        In y s ->
        In y (add x s).
    Proof.
      unfold_set.
      apply FMap.add_incr; auto.
    Qed.

    Definition remove x (s:t) : t :=
      FMap.remove x s.

    Hint Unfold remove : set.

    Theorem remove_not_in : forall x s,
        ~In x (remove x s).
    Proof.
      unfold_set.
      apply FMap.remove_not_in.
    Qed.

    Theorem remove_in : forall x s y,
        In y s ->
        x <> y ->
        In y (remove x s).
    Proof.
      unfold_set.
      apply FMap.remove_in; auto.
    Qed.

    Theorem remove_in' : forall x s y,
        In x (remove y s) ->
        In x s /\ x <> y.
    Proof.
      unfold_set.
      apply FMap.remove_in'; auto.
    Qed.

    Theorem set_extensionality : forall s1 s2,
        (forall x, In x s1 <-> In x s2) ->
        s1 = s2.
    Proof.
      unfold_set.
      apply FMap.mapsto_extensionality; intuition.
      - destruct v.
        apply _in_mapsto in H0.
        apply _in_mapsto'.
        apply H; auto.
      - destruct v.
        apply _in_mapsto in H0.
        apply _in_mapsto'.
        apply H; auto.
    Qed.

    Definition filter (P: A -> bool) (s:t) : t :=
      FMap.filter P s.

    Theorem filter_in : forall P s x,
        In x (filter P s) ->
        In x s.
    Proof.
      unfold_set.
      eauto using FMap.filter_in.
    Qed.

    Theorem filter_spec : forall P s,
        For_all (fun y => P y = true) (filter P s).
    Proof.
      unfold_set.
      eauto using FMap.filter_spec.
    Qed.

    Theorem filter_complete : forall P s x,
        In x s ->
        P x = true ->
        In x (filter P s).
    Proof.
      unfold_set.
      eauto using FMap.filter_complete.
    Qed.

    Definition is_permutation (l : list A) (s : t) : Prop :=
      forall x, List.In x l <-> In x s.

  End Sets.

End FSet.

Arguments FSet.t A {Acmp}.
