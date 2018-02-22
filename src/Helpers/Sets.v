Require Import List.
Require Import Ordering.
Require Import ProofIrrelevance.

Set Implicit Arguments.

Theorem Forall_in : forall A (P: A -> Prop) l,
    Forall P l ->
    forall x, List.In x l -> P x.
Proof.
  induction l; simpl; intros; intuition (subst; eauto).
  inversion H; eauto.
  inversion H; eauto.
Qed.

Theorem Forall_in' : forall A (P: A -> Prop) l,
    (forall x, List.In x l -> P x) ->
    Forall P l.
Proof.
  induction l; simpl; intros; eauto 10.
Qed.

Theorem Forall_subset : forall A (P: A -> Prop) (l l': list A),
    Forall P l ->
    (forall x, List.In x l' -> List.In x l) ->
    Forall P l'.
Proof.
  intros.
  eapply Forall_in'; eauto.
  intros.
  eapply Forall_in in H; eauto.
Qed.

Inductive sorted A (lt: A -> A -> Prop) : list A -> Prop :=
| sorted_nil : sorted lt nil
| sorted_cons : forall x l,
    Forall (lt x) l ->
    sorted lt l ->
    sorted lt (x::l).

Hint Constructors sorted.

Import List.ListNotations.
Open Scope list.

Module FSet.

  Section Sets.

    Variable A:Type.
    Context {Acmp: Ordering A}.

    Record t :=
      { elements: list A;
        elem_sorted: sorted cmp_lt elements }.

    Definition empty : t :=
      {| elements := [];
         elem_sorted := sorted_nil cmp_lt |}.

    Definition In x (s:t) :=
      List.In x (elements s).

    Theorem empty_in : forall x,
        ~In x empty.
    Proof.
      unfold In, empty; simpl; eauto.
    Qed.

    Definition For_all (P:A -> Prop) (s:t) :=
      Forall P (elements s).

    Theorem empty_Forall : forall P,
        For_all P empty.
    Proof.
      unfold For_all; simpl; eauto.
    Qed.

    Theorem For_all_in (P:A -> Prop) (s:t) :
      For_all P s ->
      forall x, In x s -> P x.
    Proof.
      unfold For_all, In; simpl; intros.
      eapply Forall_in; eauto.
    Qed.

    Theorem not_in_forall : forall x s,
        ~In x s ->
        For_all (fun y => x <> y) s.
    Proof.
      unfold In, For_all.
      destruct s; simpl; intros.
      clear elem_sorted0.
      induction elements0; simpl in *; eauto 10.
    Qed.

    Definition In_dec x s : {In x s} + {~In x s}.
      unfold In.
      destruct (List.in_dec cmp_dec x (elements s)); eauto.
    Defined.

    Fixpoint _add (x0:A) (l:list A) : list A :=
      match l with
      | nil => x0::nil
      | x::xs => match cmp x0 x with
                | Lt => (* x0 can go at the very beginning*)
                  x0::l
                | Gt => (* x0 should go later *)
                  x::_add x0 xs
                | Eq => (* x0 is already in the list *)
                  l
                end
      end.

    Theorem _add_forall : forall x P l,
        Forall P l ->
        P x ->
        Forall P (_add x l).
    Proof.
      induction l; simpl; intros; eauto.
      inversion H; subst; clear H.
      destruct (ord_spec x a);
        (intuition subst); eauto.
    Qed.

    Hint Resolve _add_forall.

    Theorem _add_forall' : forall x P l,
        Forall P (_add x l) ->
        Forall P l.
    Proof.
      induction l; simpl; intros; eauto.
      destruct (ord_spec x a);
        intuition subst.
      - rewrite cmp_refl in H; auto.
      - rewrite H1 in *.
        inversion H; eauto.
      - rewrite H2 in *.
        inversion H; eauto.
    Qed.

    Theorem _add_respectful : forall x l,
        sorted cmp_lt l ->
        sorted cmp_lt (_add x l).
    Proof.
      induction 1; simpl; eauto.
      destruct (ord_spec x x0); intuition subst.
      - eauto.
      - constructor; eauto.
        constructor; eauto.
        eapply Forall_impl. 2: eauto.
        intros.
        eapply cmp_trans; eauto.
      - constructor; eauto.
    Qed.

    Definition add (x:A) (s:t) : t :=
      {| elements := _add x (elements s);
         elem_sorted := _add_respectful x (elem_sorted s); |}.

    Theorem add_forall : forall x P s,
        For_all P s ->
        P x ->
        For_all P (add x s).
    Proof.
      unfold For_all, add; simpl; intros.
      eapply _add_forall; eauto.
    Qed.

    Theorem add_forall' : forall x P s,
        For_all P (add x s) ->
        For_all P s.
    Proof.
      unfold For_all, add; simpl; intros.
      eapply _add_forall'; eauto.
    Qed.

    Theorem _add_in : forall x l,
        List.In x (_add x l).
    Proof.
      induction l; simpl; eauto.
      destruct (ord_spec x a); simpl; eauto.
    Qed.

    Theorem add_in : forall x s,
        In x (add x s).
    Proof.
      unfold add, In; simpl.
      eauto using _add_in.
    Qed.

    Theorem add_in' : forall x s y,
        In x (add y s) ->
        x = y \/ In x s.
    Proof.
      destruct s as [s H].
      unfold In, add; simpl; intros.
      induction s; simpl in *; intuition eauto.
      inversion H; subst; clear H; intuition auto.
      destruct (ord_spec y a); subst; intuition.
      - rewrite cmp_refl in *.
        simpl in *; intuition auto.
      - rewrite H2 in *.
        simpl in *; intuition auto.
      - rewrite H5 in *.
        simpl in *; intuition auto.
    Qed.

    Theorem _add_incr : forall x l y,
        List.In y l ->
        List.In y (_add x l).
    Proof.
      induction l; simpl; intros; eauto.
      destruct (ord_spec x a); simpl; intuition eauto.
    Qed.

    Theorem add_incr : forall x s y,
        In y s ->
        In y (add x s).
    Proof.
      unfold add, In; simpl.
      eauto using _add_incr.
    Qed.

    Fixpoint _remove (x0:A) (l:list A) : list A :=
      match l with
      | nil => nil
      | x::xs => match cmp x0 x with
                | Lt => l
                | Eq => xs
                | Gt => x::_remove x0 xs
                end
      end.

    Theorem _remove_forall : forall x P l,
        Forall P l ->
        Forall P (_remove x l).
    Proof.
      induction 1; simpl; eauto.
      destruct (ord_spec x x0);
        subst; eauto.
    Qed.

    Hint Resolve _remove_forall.

    Theorem _remove_respectful : forall x l,
        sorted cmp_lt l ->
        sorted cmp_lt (_remove x l).
    Proof.
      induction l; simpl; intros; eauto.
      inversion H; subst; clear H.
      destruct (ord_spec x a);
        (intuition subst);
        eauto.
    Qed.

    Definition remove x (s:t) : t :=
      {| elements := _remove x (elements s);
         elem_sorted := _remove_respectful x (elem_sorted s); |}.

    Lemma forall_lt_not_in : forall x l,
        Forall (cmp_lt x) l ->
        ~List.In x l.
    Proof.
      unfold not, cmp_lt; intros.
      eapply Forall_in in H; eauto.
      rewrite cmp_refl in H; congruence.
    Qed.

    Ltac forall_in :=
      match goal with
      | [ H: Forall ?P ?l, H': List.In ?x ?l |- _ ] =>
        pose proof (Forall_in H _ H');
        clear H'
      end.

    Theorem _remove_not_in : forall x l,
        sorted cmp_lt l ->
        ~List.In x (_remove x l).
    Proof.
      unfold not; intros.
      induction l; simpl in *; eauto.
      inversion H; subst; clear H.
      destruct (ord_spec x a);
        intuition subst.
      - rewrite cmp_refl in H0.
        eapply forall_lt_not_in; eauto.
      - rewrite H1 in *.
        simpl in *; (intuition subst).
        rewrite cmp_refl in H2; congruence.
        repeat forall_in.
        congruence.
      - rewrite H2 in *.
        simpl in *; (intuition subst).
        rewrite cmp_refl in H2; congruence.
    Qed.

    Theorem remove_not_in : forall x s,
        ~In x (remove x s).
    Proof.
      unfold In, remove; simpl; intros.
      eapply _remove_not_in.
      apply (elem_sorted s).
    Qed.

    Theorem _remove_in : forall x l y,
        List.In y l ->
        x <> y ->
        List.In y (_remove x l).
    Proof.
      induction l; simpl; intuition subst.
      - destruct (ord_spec x y);
          simpl;
          (intuition subst).
      - destruct (ord_spec x a);
          simpl;
          (intuition subst).
        eauto.
    Qed.

    Theorem remove_in : forall x s y,
        In y s ->
        x <> y ->
        In y (remove x s).
    Proof.
      unfold In, remove; simpl; intros.
      auto using _remove_in.
    Qed.

    Theorem remove_in' : forall x s y,
        In x (remove y s) ->
        In x s /\ x <> y.
    Proof.
      destruct s as [s H].
      unfold In, remove; simpl; intros.
      induction s; simpl in *; eauto.
      destruct (ord_spec y a); subst.
      - rewrite cmp_refl in *.
        inversion H; subst; clear H; intuition (subst; auto).
        eapply Forall_in in H3; eauto.
        unfold cmp_lt in *; rewrite cmp_refl in *; congruence.
      - destruct H1.
        rewrite H1 in *.
        simpl in *.
        intuition (subst; eauto).
        rewrite cmp_refl in *; congruence.
        inversion H; subst; clear H; intuition eauto.
        eapply Forall_in in H3; eauto.
        congruence.
      - destruct H1.
        rewrite H2 in *.
        simpl in *; intuition (subst; eauto).
        rewrite cmp_refl in *; congruence.
        inversion H; subst; clear H; intuition eauto.
        inversion H; subst; clear H; intuition eauto.
    Qed.

    Lemma cmp_lt_antisym : forall x y,
        cmp_lt x y ->
        cmp_lt y x ->
        False.
    Proof.
      unfold cmp_lt; intros.
      apply cmp_antisym in H; congruence.
    Qed.

    Theorem set_extensionality : forall s1 s2,
        (forall x, In x s1 <-> In x s2) ->
        s1 = s2.
    Proof.
      unfold In; intros.
      destruct s1 as [s1 s1_sorted].
      destruct s2 as [s2 s2_sorted].
      simpl in *.
      assert (s1 = s2).
      generalize dependent H.
      generalize dependent s2_sorted.
      generalize dependent s1_sorted.
      eapply two_list_induction with (l1:=s1) (l2:=s2);
        simpl; intros; eauto.
      exfalso; eapply H; eauto.
      exfalso; eapply H; eauto.
      inversion s1_sorted; subst; clear s1_sorted.
      inversion s2_sorted; subst; clear s2_sorted.

      assert (~List.In x xs) by eauto using forall_lt_not_in.
      assert (~List.In y ys) by eauto using forall_lt_not_in.

      assert (x = y). {
        pose proof (H0 x).
        pose proof (H0 y).
        intuition eauto.
        repeat forall_in.
        exfalso; eauto using cmp_lt_antisym.
      } subst; f_equal.
      eapply H; eauto.
      intros.
      specialize (H0 x).
      intuition (subst; eauto);
        try solve [ exfalso; eauto using forall_lt_not_in ].
      destruct H0.
      f_equal.
      apply proof_irrelevance.
    Qed.

    Fixpoint _filter (P: A -> bool) (l: list A) : list A :=
      match l with
      | [] => []
      | x::xs => if P x then x::_filter P xs
                else _filter P xs
      end.

    Theorem _filter_in : forall P l,
        forall x, List.In x (_filter P l) ->
             List.In x l.
    Proof.
      induction l; simpl; intros; auto.
      destruct (P a); simpl in *; intuition eauto.
    Qed.

    Hint Resolve _filter_in.

    Theorem _filter_respectful : forall P l,
        sorted cmp_lt l ->
        sorted cmp_lt (_filter P l).
    Proof.
      induction l; simpl; intros; auto.
      inversion H; subst; intuition eauto.
      destruct (P a); eauto.
      constructor; eauto.
      eapply Forall_subset; eauto.
    Qed.

    Definition filter (P: A -> bool) (s:t) : t.
      refine {| elements := _filter P (elements s) |}.
      apply _filter_respectful.
      apply (elem_sorted s).
    Defined.

    Theorem filter_in : forall P s x,
        In x (filter P s) ->
        In x s.
    Proof.
      unfold In, filter; simpl; intros.
      eauto using _filter_in.
    Qed.

    Theorem filter_spec : forall P s,
        For_all (fun y => P y = true) (filter P s).
    Proof.
      unfold For_all, filter.
      destruct s as [s H].
      simpl.
      induction s; simpl; intros; auto.
      inversion H; subst; clear H; intuition.
      destruct_with_eqn (P a); eauto.
    Qed.

    Theorem filter_complete : forall P s x,
        In x s ->
        P x = true ->
        In x (filter P s).
    Proof.
      destruct s as [s H].
      unfold In, filter; simpl; intros.
      induction s; simpl; intros; auto.
      inversion H; subst; clear H; intuition.
      simpl in H0.
      destruct_with_eqn (P a); simpl; intuition eauto.
      subst; eauto.
      congruence.
    Qed.

  End Sets.

  Arguments t A {Acmp}.
  Arguments empty {A} {Acmp}.

End FSet.
