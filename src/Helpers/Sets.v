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

Lemma Forall_map : forall A (l: list A) B (f: A -> B) (P: B -> Prop),
    Forall P (map f l) <->
    Forall (fun x => P (f x)) l.
Proof.
  induction l; simpl; intuition eauto.
  - inversion H; subst; clear H.
    constructor; eauto.
    apply IHl; auto.
  - inversion H; subst; clear H.
    constructor; eauto.
    apply IHl; auto.
Qed.

Hint Constructors sorted.

Import List.ListNotations.
Open Scope list.

Module FMap.

  Section Maps.

    Variable A:Type.
    Variable V:Type.
    Context {Acmp: Ordering A}.

    Record t :=
      { elements: list (A * V);
        keys := map fst elements;
        elem_sorted: sorted cmp_lt keys }.

    Definition empty : t :=
      {| elements := [];
         elem_sorted := sorted_nil cmp_lt |}.

    Definition MapsTo (x:A) (v:V) (s:t) :=
      List.In (x, v) (elements s).

    Definition In (x:A) (s:t) :=
      List.In x (keys s).

    Theorem empty_mapsto : forall x v,
        ~MapsTo x v empty.
    Proof.
      compute; auto.
    Qed.

    Theorem empty_in : forall x,
        ~In x empty.
    Proof.
      compute; eauto.
    Qed.

    Lemma cmp_lt_irrefl : forall x,
        cmp_lt x x -> False.
    Proof.
      unfold cmp_lt; intros.
      rewrite cmp_refl in *; congruence.
    Qed.

    Hint Resolve cmp_lt_irrefl : falso.

    Hint Extern 4 => exfalso; eauto with falso nocore.

    Lemma Forall_fst : forall P (l: list (A * V)) x v,
        Forall P (map fst l) ->
        List.In (x, v) l ->
        P x.
    Proof.
      intros.
      apply -> Forall_map in H.
      eapply Forall_in in H; eauto.
      auto.
    Qed.

    Ltac forall_in :=
      match goal with
      | [ H: Forall ?P ?l, H': List.In ?x ?l |- _ ] =>
        let Hnew := fresh in
        pose proof (Forall_in H _ H') as Hnew;
        clear H';
        simpl in Hnew
      | [ H: Forall ?P (map fst ?l), H': List.In (?x, ?v) ?l |- _ ] =>
        let Hnew := fresh in
        pose proof (Forall_fst l x v H H') as Hnew;
        clear H';
        simpl in Hnew
      end.

    Lemma all_keys_lt : forall (l: list (A*V)) (x:A),
        Forall (cmp_lt x) (map fst l) ->
        forall v, ~List.In (x, v) l.
    Proof.
      unfold not; intros.
      repeat forall_in; eauto.
    Qed.

    Lemma all_keys_lt_false : forall (l: list (A*V)) (x:A),
        Forall (cmp_lt x) (map fst l) ->
        forall v, List.In (x, v) l -> False.
    Proof.
      apply all_keys_lt.
    Qed.

    Hint Resolve all_keys_lt_false : falso.

    Ltac abstract_map m :=
      pose proof (elem_sorted m);
      unfold keys in *;
      generalize dependent (elements m); clear m.

    Theorem mapsto_unique : forall x v v' m,
        MapsTo x v m ->
        MapsTo x v' m ->
        v = v'.
    Proof.
      unfold MapsTo; intros.
      abstract_map m.
      induction l; simpl in *; intros; eauto.
      destruct a as [x' v'']; simpl in *.
      inversion_clear H1.
      intuition (subst; eauto);
        repeat match goal with
               | [ H: (_, _) = (_, _) |- _ ] =>
                 inversion H; subst; clear H
               end;
        eauto.
    Qed.

    Definition For_all (P:A*V -> Prop) (s:t) :=
      Forall P (elements s).

    Theorem empty_Forall : forall P,
        For_all P empty.
    Proof.
      compute; eauto.
    Qed.

    Theorem For_all_in (P:A*V -> Prop) (s:t) :
      For_all P s ->
      forall x v, MapsTo x v s -> P (x, v).
    Proof.
      unfold For_all, MapsTo; simpl; intros.
      eapply Forall_in; eauto.
    Qed.

    Theorem not_in_forall : forall x s,
        ~In x s ->
        For_all (fun y => x <> fst y) s.
    Proof.
      unfold In, For_all.
      destruct s; simpl; intros.
      unfold keys in *; simpl in *.
      clear elem_sorted0.
      induction elements0; simpl in *; eauto 10.
    Qed.

    Definition In_dec x s : {In x s} + {~In x s}.
      unfold In.
      apply (List.in_dec cmp_dec x (keys s)).
    Defined.

    Fixpoint _add (x0:A) (v0:V) (l:list (A*V)) : list (A*V) :=
      match l with
      | nil => (x0,v0)::nil
      | (x,v)::xs => match cmp x0 x with
                    | Lt => (* x0 can go at the very beginning*)
                      (x0,v0)::l
                    | Gt => (* x0 should go later *)
                      (x,v)::_add x0 v0 xs
                    | Eq => (* x0 is already in the list *)
                      (x,v0)::xs
                    end
      end.

    Fixpoint _add_key (x0:A) (l:list A) : list A :=
      match l with
      | nil => x0::nil
      | x::xs => match cmp x0 x with
                    | Lt => (* x0 can go at the very beginning*)
                      x0::l
                    | Gt => (* x0 should go later *)
                      x::_add_key x0 xs
                    | Eq => (* x0 is already in the list *)
                      l
                    end
      end.

    Theorem _add_key_keys : forall x v (l: list (A*V)),
        map fst (_add x v l) = _add_key x (map fst l).
    Proof.
      induction l; simpl; auto.
      destruct a; simpl.
      destruct (cmp x a); simpl; auto.
      congruence.
    Qed.

    Theorem _add_forall : forall x v P l,
        Forall P l ->
        P (x, v) ->
        Forall P (_add x v l).
    Proof.
      induction l; simpl; intros; eauto.
      inversion H; subst; clear H.
      destruct a as [x' v'].
      destruct (ord_spec x x');
        (intuition subst); eauto.
    Qed.

    Hint Resolve _add_forall.

    Theorem _add_forall' : forall x v P l,
        ~List.In x (map fst l) ->
        Forall P (_add x v l) ->
        Forall P l.
    Proof.
      induction l; simpl; intros; eauto.
      destruct a as [x' v'].
      destruct (ord_spec x x');
        simpl in *;
        intuition subst.
      - congruence.
      - rewrite H2 in *.
        inversion H0; eauto.
      - rewrite H3 in *.
        inversion H0; eauto.
    Qed.

    Theorem _add_key_forall : forall x P l,
        Forall P l ->
        P x ->
        Forall P (_add_key x l).
    Proof.
      induction l; simpl; intros; eauto.
      inversion H; subst; clear H.
      destruct (ord_spec x a);
        (intuition subst); eauto.
    Qed.

    Hint Resolve _add_key_forall.

    Theorem _add_respectful : forall x v l,
        sorted cmp_lt (map fst l) ->
        sorted cmp_lt (map fst (_add x v l)).
    Proof.
      intros.
      rewrite _add_key_keys.
      generalize dependent (map fst l); clear l.
      induction 1; simpl; eauto.
      destruct (ord_spec x x0); intuition subst.
      - eauto.
      - constructor; eauto.
        constructor; eauto.
        eapply Forall_impl; [ | eauto ].
        intros.
        eapply cmp_trans; eauto.
      - constructor; eauto.
    Qed.

    Definition add (x:A) (v:V) (s:t) : t :=
      {| elements := _add x v (elements s);
         elem_sorted := _add_respectful
                          x v (elements s) (elem_sorted s); |}.

    Theorem add_forall : forall x v P s,
        For_all P s ->
        P (x, v) ->
        For_all P (add x v s).
    Proof.
      unfold For_all, add; simpl; intros.
      eapply _add_forall; eauto.
    Qed.

    Theorem add_forall' : forall x v P s,
        ~In x s ->
        For_all P (add x v s) ->
        For_all P s.
    Proof.
      unfold For_all, add; simpl; intros.
      eapply _add_forall'; eauto.
    Qed.

    Theorem _add_mapsto : forall x v l,
        List.In (x, v) (_add x v l).
    Proof.
      induction l; simpl; eauto.
      destruct a as [x' v'].
      destruct (ord_spec x x'); subst; simpl; eauto.
    Qed.

    Theorem _add_in : forall x v l,
        List.In x (map fst (_add x v l)).
    Proof.
      induction l; simpl; eauto.
      destruct a as [x' v'].
      destruct (ord_spec x x'); subst; simpl; eauto.
    Qed.

    Theorem add_mapsto : forall x v s,
        MapsTo x v (add x v s).
    Proof.
      unfold add, MapsTo; simpl.
      unfold keys; simpl; intros.
      eapply _add_mapsto.
    Qed.

    Theorem add_in : forall x v s,
        In x (add x v s).
    Proof.
      unfold add, In; simpl.
      unfold keys; simpl; intros.
      eapply _add_in.
    Qed.

    Theorem add_in' : forall x s y v,
        In x (add y v s) ->
        x = y \/ In x s.
    Proof.
      destruct s as [s H].
      unfold In, add; simpl; intros.
      induction s; simpl in *; intuition eauto.
      subst H.
      compute [keys elements] in *.
      destruct a as [y' v'].
      inversion elem_sorted0; subst; clear elem_sorted0; intuition auto.
      destruct (ord_spec y y'); subst; intuition.
      - rewrite cmp_refl in *.
        simpl in *; intuition auto.
      - rewrite H4 in *; intuition eauto.
        simpl in *; intuition auto.
      - rewrite H5 in *.
        simpl in *; intuition auto.
    Qed.

    Fixpoint _remove (x0:A) (l:list (A*V)) : list (A*V) :=
      match l with
      | nil => nil
      | (x,v)::xs => match cmp x0 x with
                | Lt => l
                | Eq => xs
                | Gt => (x,v)::_remove x0 xs
                end
      end.

    Fixpoint _remove_key (x0:A) (l:list A) : list A :=
      match l with
      | nil => nil
      | x::xs => match cmp x0 x with
                | Lt => l
                | Eq => xs
                | Gt => x::_remove_key x0 xs
                end
      end.

    Theorem _remove_key_keys : forall x (l: list (A*V)),
        map fst (_remove x l) = _remove_key x (map fst l).
    Proof.
      induction l; simpl; auto.
      destruct a as [x' v]; simpl.
      destruct (cmp x x'); simpl; congruence.
    Qed.

    Theorem _remove_forall : forall x P l,
        Forall P l ->
        Forall P (_remove x l).
    Proof.
      induction 1; simpl; eauto.
      destruct x0 as [x' v].
      destruct (ord_spec x x');
        subst; eauto.
    Qed.

    Hint Resolve _remove_forall.

    Theorem _remove_key_forall : forall x P l,
        Forall P l ->
        Forall P (_remove_key x l).
    Proof.
      induction 1; simpl; eauto.
      destruct (ord_spec x x0);
        subst; eauto.
    Qed.

    Hint Resolve _remove_key_forall.

    Theorem _remove_respectful : forall x l,
        sorted cmp_lt (map fst l) ->
        sorted cmp_lt (map fst (_remove x l)).
    Proof.
      intros.
      rewrite _remove_key_keys.
      generalize dependent (map fst l); clear l.
      induction l; simpl; intros; eauto.
      inversion H; subst; clear H.
      destruct (ord_spec x a);
        (intuition subst);
        eauto.
    Qed.

    Definition remove x (s:t) : t :=
      {| elements := _remove x (elements s);
         elem_sorted := _remove_respectful
                          x (elements s) (elem_sorted s); |}.

    Lemma forall_lt_not_in : forall x l,
        Forall (cmp_lt x) l ->
        ~List.In x l.
    Proof.
      unfold not, cmp_lt; intros.
      eapply Forall_in in H; eauto.
    Qed.

    Theorem _remove_not_in : forall x l,
        sorted cmp_lt l ->
        ~List.In x (_remove_key x l).
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
      unfold In, remove, keys; simpl; intros.
      rewrite _remove_key_keys.
      eapply _remove_not_in.
      apply (elem_sorted s).
    Qed.

    Theorem _remove_mapsto : forall x l y v,
        List.In (y, v) l ->
        x <> y ->
        List.In (y, v) (_remove x l).
    Proof.
      induction l; simpl; intuition subst.
      - inversion_clear H1.
        destruct (ord_spec x y);
          simpl;
          (intuition subst).
      - destruct (ord_spec x a0);
          simpl;
          (intuition subst).
        eauto.
    Qed.

    Theorem _remove_in : forall x l y,
        List.In y l ->
        x <> y ->
        List.In y (_remove_key x l).
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

    Theorem remove_mapsto : forall x s y v,
        MapsTo y v s ->
        x <> y ->
        MapsTo y v (remove x s).
    Proof.
      unfold MapsTo, remove, keys; simpl; intros.
      auto using _remove_mapsto.
    Qed.

    Theorem remove_in : forall x s y,
        In y s ->
        x <> y ->
        In y (remove x s).
    Proof.
      unfold In, remove, keys; simpl; intros.
      rewrite _remove_key_keys.
      auto using _remove_in.
    Qed.

    Theorem remove_in' : forall x s y,
        In x (remove y s) ->
        In x s /\ x <> y.
    Proof.
      destruct s as [s H].
      unfold In, remove, keys; simpl; intros.
      induction s; simpl in *; eauto.
      destruct a as [y' v'].
      subst H; simpl in *.
      destruct (ord_spec y y'); subst.
      - rewrite cmp_refl in *.
        inversion elem_sorted0; subst; clear elem_sorted0;
          intuition (subst; auto).
        eapply Forall_in in H2; eauto.
      - destruct H.
        rewrite H in *; simpl in *.
        intuition (subst; eauto).
        inversion elem_sorted0; subst; clear elem_sorted0;
          intuition eauto.
        forall_in; congruence.
      - destruct H.
        rewrite H1 in *; simpl in *.
        intuition (subst; eauto).
        inversion_clear elem_sorted0; intuition eauto.
        inversion_clear elem_sorted0; intuition eauto.
    Qed.

    Lemma cmp_lt_antisym : forall x y,
        cmp_lt x y ->
        cmp_lt y x ->
        False.
    Proof.
      unfold cmp_lt; intros.
      apply cmp_antisym in H; congruence.
    Qed.

    Hint Resolve cmp_lt_antisym : falso.

    Theorem mapsto_extensionality : forall s1 s2,
        (forall x v, MapsTo x v s1 <-> MapsTo x v s2) ->
        s1 = s2.
    Proof.
      unfold In; intros.
      destruct s1 as [s1 ? s1_sorted].
      destruct s2 as [s2 ? s2_sorted].
      subst keys0 keys1.
      unfold MapsTo, keys in *; simpl in *.
      assert (s1 = s2).
      generalize dependent H.
      generalize dependent s2_sorted.
      generalize dependent s1_sorted.
      eapply two_list_induction with (l1:=s1) (l2:=s2);
        simpl; intros; eauto.
      destruct y as [x v].
      exfalso; eapply H; eauto.
      destruct x as [x v].
      exfalso; eapply H; eauto.
      inversion s1_sorted; subst; clear s1_sorted.
      inversion s2_sorted; subst; clear s2_sorted.
      intuition idtac.

      destruct x as [x v1].
      destruct y as [y v2].
      simpl in *.
      assert (~List.In (x, v1) xs) by eauto using all_keys_lt.
      assert (~List.In (y, v2) ys) by eauto using all_keys_lt.

      assert (x = y /\ v1 = v2). {
        pose proof (H0 x v1).
        pose proof (H0 y v2).
        (intuition eauto);
          repeat match goal with
                 | [ H: (_, _) = (_, _) |- _ ] =>
                   inversion H; subst; clear H
                 end;
          intuition idtac.
        repeat forall_in; eauto.
        repeat forall_in; eauto.
      } intuition subst; f_equal.
      eapply H; eauto.
      intros.
      pose proof (H0 x v).
      (intuition eauto);
        repeat match goal with
               | [ H: (_, _) = (_, _) |- _ ] =>
                 inversion H; subst; clear H
               end;
        intuition idtac.
      destruct H0.
      f_equal.
      apply proof_irrelevance.
    Qed.

    Fixpoint _filter (P: A -> bool) (l: list (A*V)) : list (A*V) :=
      match l with
      | [] => []
      | (x,v)::xs => if P x then (x,v)::_filter P xs
                else _filter P xs
      end.

    Fixpoint _filter_key (P: A -> bool) (l: list A) : list A :=
      match l with
      | [] => []
      | x::xs => if P x then x::_filter_key P xs
                else _filter_key P xs
      end.

    Theorem _filter_key_keys : forall P l,
        map fst (_filter P l) = _filter_key P (map fst l).
    Proof.
      induction l; simpl; auto.
      destruct a as [x v]; simpl.
      destruct (P x); simpl; congruence.
    Qed.

    Theorem _filter_in : forall P l,
        forall x v, List.In (x, v) (_filter P l) ->
               List.In (x, v) l.
    Proof.
      induction l; simpl; intros; auto.
      destruct a as [x' v'].
      destruct (P x'); simpl in *; intuition eauto.
    Qed.

    Theorem _filter_key_in : forall P l,
        forall x, List.In x (_filter_key P l) ->
             List.In x l.
    Proof.
      induction l; simpl; intros; auto.
      destruct (P a); simpl in *; intuition eauto.
    Qed.

    Hint Resolve _filter_key_in.

    Theorem _filter_respectful : forall P l,
        sorted cmp_lt (map fst l) ->
        sorted cmp_lt (map fst (_filter P l)).
    Proof.
      intros.
      rewrite _filter_key_keys.
      generalize dependent (map fst l); clear l.
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
      unfold In, filter, keys; simpl; intros.
      rewrite _filter_key_keys in *.
      eauto using _filter_in.
    Qed.

    Theorem filter_spec : forall P s,
        For_all (fun '(x, _) => P x = true) (filter P s).
    Proof.
      unfold For_all, filter.
      destruct s as [s H].
      simpl.
      subst H.
      induction s; simpl; intros; auto.
      destruct a as [x v]; simpl in *.
      inversion elem_sorted0; subst; clear elem_sorted0; intuition.
      destruct_with_eqn (P x); eauto.
    Qed.

    Theorem filter_complete : forall P s x,
        In x s ->
        P x = true ->
        In x (filter P s).
    Proof.
      destruct s as [s H].
      unfold In, filter, keys; simpl; intros.
      subst H.
      induction s; simpl; intros; auto.
      destruct a as [x' v']; simpl in *.
      inversion elem_sorted0; subst; clear elem_sorted0; intuition.
      - subst.
        destruct_with_eqn (P x); simpl; intuition eauto.
        congruence.
      - destruct_with_eqn (P x'); simpl; intuition eauto.
    Qed.

  End Maps.

  Arguments t A V {Acmp}.
  Arguments empty {A} {V} {Acmp}.

End FMap.
