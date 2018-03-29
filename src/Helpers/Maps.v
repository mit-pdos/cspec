Require Import List.
Require Import Ordering.
Require Import ProofIrrelevance.
Require Import Helpers.

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

    Hint Unfold In MapsTo elements keys : map.

    Ltac unfold_map :=
      autounfold with map in *;
      intros;
      repeat match goal with
             | [ m: t |- _ ] =>
               let l := fresh "l" in
               destruct m as [l ?]
             | [ keys := _ |- _ ] =>
               subst keys
             end;
      cbv [elements keys] in *.

    Ltac inv H :=
      inversion H; subst; clear H.

    Ltac simp :=
      subst;
      repeat match goal with
             | |- forall _, _ => intros
             | [ a: A * V |- _ ] =>
               let x := fresh "x" in
               let v := fresh "v" in
               destruct a as [x v];
               cbn [fst snd] in *
             | [ H: (_,_) = (_,_) |- _ ] => inv H
             | [ H: sorted _ (_::_) |- _ ] => inv H
             | [ H: Forall _ (_::_) |- _ ] => inv H
             | [ H: _ /\ _ |- _ ] => destruct H
             | [ H: ?P -> _, H': ?P |- _ ] =>
               lazymatch type of P with
               | Prop => specialize (H H')
               end
             | [ H: context[cmp ?x ?y],
                    H': cmp ?x ?y = _ |- _ ] =>
               rewrite H' in H
             | _ => progress simpl in *
             end;
      eauto.

    Ltac cmp_split :=
      let t x y :=
          destruct (ord_spec x y);
          simp;
          try solve [ intuition eauto ] in
      match goal with
      | |- context[cmp ?x ?y] => t x y
      | [ H: context[cmp ?x ?y] |- _ ] => t x y
      end.

    Theorem mapsto_unique : forall x v v' m,
        MapsTo x v m ->
        MapsTo x v' m ->
        v = v'.
    Proof.
      unfold_map.
      induction l; simp.
      intuition simp.
    Qed.

    Lemma mapsto_in : forall a v m,
        MapsTo a v m ->
        In a m.
    Proof.
      unfold_map.
      induction l; simp.
      intuition simp.
    Qed.

    Fixpoint get_opt (x0:A) (l:list (A*V)) : option V :=
      match l with
      | nil => None
      | (x,v)::xs => if cmp_dec x x0 then Some v else get_opt x0 xs
      end.

    Definition in_mapsto_get a m :
        In a m ->
        {v | MapsTo a v m}.
    Proof.
      unfold_map.
      destruct_with_eqn (get_opt a l).
      exists v.
      induction l; simp.
      intuition simp.
      destruct (cmp_dec a a); subst; try congruence.
      inv Heqo; eauto.
      destruct (cmp_dec x a); subst.
      inv Heqo; eauto.
      intuition eauto.

      exfalso.
      induction l; simp.
      destruct (cmp_dec x a); subst; try congruence.
      intuition eauto.
    Defined.

    Lemma in_mapsto_exists : forall a m,
        In a m ->
        exists v, MapsTo a v m.
    Proof.
      intros.
      destruct (in_mapsto_get a m); eauto.
    Qed.

    Lemma sorted_distinct : forall a b l1 l2,
      sorted cmp_lt (a :: l1 ++ b :: l2) ->
      a <> b.
    Proof.
      intros.
      inversion H; clear H; subst.
      clear H3.
      eapply Forall_forall with (x := b) in H2.
      - intro.
        unfold cmp_lt in *.
        destruct (cmp_eq a b).
        intuition.
        congruence.
      - eapply in_or_app. right. constructor. eauto.
    Qed.

    Definition For_all (P:A*V -> Prop) (s:t) :=
      Forall P (elements s).

    Hint Unfold For_all : map.

    Theorem empty_Forall : forall P,
        For_all P empty.
    Proof.
      compute; eauto.
    Qed.

    Theorem For_all_in (P:A*V -> Prop) (s:t) :
      For_all P s ->
      forall x v, MapsTo x v s -> P (x, v).
    Proof.
      unfold_map.
      eapply Forall_in; eauto.
    Qed.

    Theorem not_in_forall : forall x s,
        ~In x s ->
        For_all (fun y => x <> fst y) s.
    Proof.
      unfold_map.
      induction l; simp; eauto 10.
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
      induction l; simp.
      cmp_split; congruence.
    Qed.

    Theorem _add_forall : forall x v P l,
        Forall P l ->
        P (x, v) ->
        Forall P (_add x v l).
    Proof.
      induction l; simp.
      cmp_split.
    Qed.

    Hint Resolve _add_forall.

    Theorem _add_forall' : forall x v P l,
        ~List.In x (map fst l) ->
        Forall P (_add x v l) ->
        Forall P l.
    Proof.
      induction l; simp.
      cmp_split.
    Qed.

    Theorem _add_key_forall : forall x P l,
        Forall P l ->
        P x ->
        Forall P (_add_key x l).
    Proof.
      induction l; simp.
      cmp_split.
    Qed.

    Hint Resolve _add_key_forall.

    Ltac abstract_keys :=
      match goal with
      | |- context[map fst ?l] =>
        generalize dependent (map fst l); clear l
      end.

    Theorem _add_respectful : forall x v l,
        sorted cmp_lt (map fst l) ->
        sorted cmp_lt (map fst (_add x v l)).
    Proof.
      intros.
      rewrite _add_key_keys.
      abstract_keys.
      induction 1; simp.
      cmp_split.
      constructor; eauto.
      constructor; eauto.
      eapply Forall_impl; [ | eauto ].
      intros.
      eapply cmp_trans; eauto.
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
      unfold_map; simp.
    Qed.

    Theorem add_forall' : forall x v P s,
        ~In x s ->
        For_all P (add x v s) ->
        For_all P s.
    Proof.
      unfold_map; simp.
      eapply _add_forall'; eauto.
    Qed.

    Theorem add_forall'_in : forall x v v0 (P: A*V -> Prop) s,
        MapsTo x v0 s ->
        P (x, v0) ->
        For_all P (add x v s) ->
        For_all P s.
    Proof.
      unfold_map; simp.
      induction l; simp.
      cmp_split.
      intuition simp.
      rewrite cmp_refl in *; simp.
      intuition simp.
    Qed.

    Theorem _add_mapsto : forall x v l,
        List.In (x, v) (_add x v l).
    Proof.
      induction l; simp.
      cmp_split.
    Qed.

    Theorem _add_in : forall x v l,
        List.In x (map fst (_add x v l)).
    Proof.
      induction l; simp.
      cmp_split.
    Qed.

    Theorem add_mapsto : forall x v s,
        MapsTo x v (add x v s).
    Proof.
      unfold_map; simp.
      eapply _add_mapsto.
    Qed.

    Theorem add_in : forall x v s,
        In x (add x v s).
    Proof.
      unfold_map; simp.
      eapply _add_in.
    Qed.

    Hint Unfold add : map.

    Theorem add_incr : forall x v s y,
        In y s ->
        In y (add x v s).
    Proof.
      unfold_map; simp.
      induction l; simp.
      cmp_split.
    Qed.

    Theorem in_add : forall a1 a2 v m,
        In a1 m ->
        In a1 (add a2 v m).
    Proof.
      unfold_map.
      rewrite _add_key_keys.
      abstract_keys.
      induction l; simp.
      cmp_split.
    Qed.

    Theorem add_in' : forall x s y v,
        In x (add y v s) ->
        x = y \/ In x s.
    Proof.
      unfold_map.
      induction l; simp.
      intuition.
      cmp_split.
      rewrite cmp_refl in *; simp.
    Qed.

    Theorem in_add_ne : forall a1 a2 v m,
        In a1 (add a2 v m) ->
        a1 <> a2 ->
        In a1 m.
    Proof.
      intros.
      apply add_in' in H; intuition eauto.
    Qed.

    Theorem add_in_in : forall a1 a2 v m,
        In a2 m ->
        In a1 (add a2 v m) ->
        In a1 m.
    Proof.
      intros.
      eapply add_in' in H0; intuition eauto.
      subst; eauto.
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
      induction l; simp.
      cmp_split.
      congruence.
    Qed.

    Theorem _remove_forall : forall x P l,
        Forall P l ->
        Forall P (_remove x l).
    Proof.
      induction 1; simp.
      cmp_split.
    Qed.

    Hint Resolve _remove_forall.

    Theorem _remove_key_forall : forall x P l,
        Forall P l ->
        Forall P (_remove_key x l).
    Proof.
      induction 1; simp.
      cmp_split.
    Qed.

    Hint Resolve _remove_key_forall.

    Theorem _remove_respectful : forall x l,
        sorted cmp_lt (map fst l) ->
        sorted cmp_lt (map fst (_remove x l)).
    Proof.
      intros.
      rewrite _remove_key_keys.
      abstract_keys.
      induction l; simp.
      cmp_split.
    Qed.

    Definition remove x (s:t) : t :=
      {| elements := _remove x (elements s);
         elem_sorted := _remove_respectful
                          x (elements s) (elem_sorted s); |}.

    Lemma forall_lt_not_in : forall x l,
        Forall (cmp_lt x) l ->
        ~List.In x l.
    Proof.
      unfold_map.
      intro.
      forall_in.
      eauto.
    Qed.

    Lemma forall_lt_not_in_False : forall x l,
        Forall (cmp_lt x) l ->
        List.In x l ->
        False.
    Proof.
      apply forall_lt_not_in.
    Qed.

    Hint Resolve forall_lt_not_in_False : falso.

    Theorem _remove_not_in : forall x l,
        sorted cmp_lt l ->
        ~List.In x (_remove_key x l).
    Proof.
      unfold not; intros.
      induction l; simp.
      cmp_split.
      rewrite cmp_refl in *; eauto.

      intuition simp.
      forall_in; congruence.
      intuition simp.
    Qed.

    Hint Unfold remove : map.

    Theorem remove_not_in : forall x s,
        ~In x (remove x s).
    Proof.
      unfold_map.
      rewrite _remove_key_keys.
      eapply _remove_not_in; auto.
    Qed.

    Lemma _wlog_and : forall (P Q: Prop),
        P ->
        (P -> Q) ->
        P /\ Q.
    Proof.
      firstorder.
    Qed.

    Lemma mapsto_remove : forall a1 a2 v m,
        MapsTo a1 v (remove a2 m) ->
        a1 <> a2 /\ MapsTo a1 v m.
    Proof.
      intros.
      apply _wlog_and.
      intro; subst.
      apply mapsto_in in H.
      apply remove_not_in in H; auto.

      unfold_map.
      induction l; simp.
      cmp_split.
      rewrite cmp_refl in *.
      intuition eauto.
    Qed.

    Theorem _remove_mapsto : forall x l y v,
        List.In (y, v) l ->
        x <> y ->
        List.In (y, v) (_remove x l).
    Proof.
      induction l; simp.
      cmp_split.
      intuition simp.
    Qed.

    Theorem _remove_in : forall x l y,
        List.In y l ->
        x <> y ->
        List.In y (_remove_key x l).
    Proof.
      induction l; simp.
      cmp_split.
    Qed.

    Theorem remove_mapsto : forall x s y v,
        MapsTo y v s ->
        x <> y ->
        MapsTo y v (remove x s).
    Proof.
      unfold_map; simp.
      auto using _remove_mapsto.
    Qed.

    Theorem remove_in : forall x s y,
        In y s ->
        x <> y ->
        In y (remove x s).
    Proof.
      unfold_map; simp.
      rewrite _remove_key_keys.
      eauto using _remove_in.
    Qed.

    Theorem remove_in' : forall x s y,
        In x (remove y s) ->
        In x s /\ x <> y.
    Proof.
      unfold_map; simp.
      induction l; simp.
      cmp_split.
      - rewrite cmp_refl in *.
        intuition simp.
      - intuition (simp; try congruence).
        forall_in; congruence.
      - intuition (simp; try congruence).
    Qed.

    Theorem in_remove : forall a1 a2 m,
        In a1 (remove a2 m) ->
        In a1 m.
    Proof.
      intros.
      eapply remove_in'; eauto.
    Qed.

    Theorem in_remove_ne : forall a1 a2 m,
        In a1 m ->
        a1 <> a2 ->
        In a1 (remove a2 m).
    Proof.
      intros.
      apply remove_in; auto.
    Qed.

    Lemma elements_eq : forall m1 m2,
        elements m1 = elements m2 ->
        m1 = m2.
    Proof.
      unfold_map.
      destruct H.
      f_equal.
      apply proof_irrelevance.
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
      intros.
      apply elements_eq.
      unfold_map.

      rename l into l1.
      rename l0 into l2.
      generalize dependent H.
      generalize dependent elem_sorted1.
      generalize dependent elem_sorted0.
      eapply two_list_induction with (l1:=l1) (l2:=l2); simp.
      exfalso; eapply H; eauto.
      exfalso; eapply H; eauto.

      rename x0 into x;
        rename x1 into y.
      rename v into v1;
        rename v0 into v2.
      assert (x = y /\ v1 = v2).
      pose proof (H0 x v1).
      pose proof (H0 y v2).
      intuition simp.
      repeat forall_in; eauto.
      repeat forall_in; eauto.
      intuition subst; f_equal.

      eapply H; intros.
      pose proof (H0 x v).
      intuition simp.
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
      induction l; simp.
      destruct (P x); simpl; congruence.
    Qed.

    Theorem _filter_in : forall P l,
        forall x v, List.In (x, v) (_filter P l) ->
               List.In (x, v) l.
    Proof.
      induction l; simp.
      destruct (P x0); simpl in *; intuition eauto.
    Qed.

    Theorem _filter_key_in : forall P l,
        forall x, List.In x (_filter_key P l) ->
             List.In x l.
    Proof.
      induction l; simp.
      destruct (P a); simpl in *; intuition eauto.
    Qed.

    Hint Resolve _filter_key_in.

    Theorem _filter_respectful : forall P l,
        sorted cmp_lt (map fst l) ->
        sorted cmp_lt (map fst (_filter P l)).
    Proof.
      intros.
      rewrite _filter_key_keys.
      abstract_keys.
      induction l; simp.
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
      unfold_map; simp.
      rewrite _filter_key_keys in *.
      eauto using _filter_in.
    Qed.

    Hint Unfold filter : map.

    Theorem filter_spec : forall P s,
        For_all (fun '(x, _) => P x = true) (filter P s).
    Proof.
      unfold_map.
      induction l; simp.
      destruct_with_eqn (P x); eauto.
    Qed.

    Theorem filter_complete : forall P s x,
        In x s ->
        P x = true ->
        In x (filter P s).
    Proof.
      unfold_map.
      induction l; simp.
      destruct_with_eqn (P x0);
        intuition simp.
      congruence.
    Qed.

    Theorem filter_holds : forall P s x,
        In x (filter P s) ->
        P x = true.
    Proof.
      unfold_map.
      induction l; simp.
      destruct_with_eqn (P x0);
        intuition simp.
      intuition congruence.
    Qed.

    (* whole-map equational specifications *)

    (* intuition is creating extra typeclass obligations that aren't true *)
    Ltac intuit :=
      repeat match goal with
             | [ H: _ \/ _ |- _ ] => destruct H
             | |- _ /\ _ => split
             end; simp.

    Theorem mapsto_add_ne :
      forall a1 v1 a2 v2 m,
        MapsTo a1 v1 (add a2 v2 m) ->
        a1 <> a2 ->
        MapsTo a1 v1 m.
    Proof.
      unfold_map; simp.
      induction l; simp.
      intuition simp.
      cmp_split.
      rewrite cmp_refl in *; simp.
      intuit.
      intuit.
    Qed.

    Theorem mapsto_add_eq :
      forall a1 v1 a2 v2 m,
        MapsTo a1 v1 (add a2 v2 m) ->
        a1 = a2 ->
        v1 = v2.
    Proof.
      unfold_map; simp.
      induction l; simp.
      intuition simp.
      cmp_split.
      rewrite cmp_refl in *; simp.
      intuit.
      intuit.
      forall_in; congruence.
      intuit.
    Qed.

    Theorem mapsto_add_ne' :
      forall a1 v1 a2 v2 m,
        MapsTo a1 v1 m ->
        a1 <> a2 ->
        MapsTo a1 v1 (add a2 v2 m).
    Proof.
      unfold_map; simp.
      induction l; simp.
      cmp_split.
      destruct H; simp.
    Qed.

    Theorem mapsto_add_or :
      forall a1 v1 a2 v2 m,
        MapsTo a1 v1 (add a2 v2 m) ->
        a1 = a2 /\ v1 = v2 \/
        a1 <> a2 /\ MapsTo a1 v1 m.
    Proof.
      intros.
      destruct (cmp_dec a1 a2); subst.
      - eapply mapsto_add_eq in H; eauto.
      - eapply mapsto_add_ne in H; eauto.
    Qed.

    Lemma mapsto_ext_sym : forall T (m1 m2: T -> t),
        (forall t, forall a v, MapsTo a v (m1 t) -> MapsTo a v (m2 t)) ->
        (forall t, (forall a v, MapsTo a v (m1 t) -> MapsTo a v (m2 t)) ->
              (forall a v, MapsTo a v (m2 t) -> MapsTo a v (m1 t))) ->
        (forall t, m1 t = m2 t).
    Proof.
      intros.
      apply mapsto_extensionality; intuition.
    Qed.

    Ltac fwd :=
      subst;
      repeat match goal with
             | [ H: MapsTo ?a _ (add ?a _ _) |- _ ] =>
               apply mapsto_add_eq in H; auto; simp
             | [ |- MapsTo ?a1 _ (add ?a2 _ _) ] =>
               assert (a1 <> a2) by auto;
               apply mapsto_add_ne'; [ | solve [auto] ]
             | [ |- MapsTo ?a _ (add ?a _ _) ] =>
               apply add_mapsto
             | [ H: MapsTo ?a1 _ (add ?a2 _ _) |- _ ] =>
               apply mapsto_add_ne in H; [ | solve [auto] ]
             | [ |- MapsTo ?a1 _ (remove ?a2 _) ] =>
               apply remove_mapsto; [ | solve [auto] ]
             | [ H: MapsTo _ _ (remove _ _) |- _ ] =>
               apply mapsto_remove in H; destruct H
             | _ => assumption
             end.

    Theorem add_add_ne :
      forall a1 v1 a2 v2 m,
        a1 <> a2 ->
        add a1 v1 (add a2 v2 m) = add a2 v2 (add a1 v1 m).
    Proof.
      intros.
      apply mapsto_extensionality; intuition idtac.
      - destruct (cmp_dec x a1), (cmp_dec x a2); fwd.
      - destruct (cmp_dec x a1), (cmp_dec x a2); fwd.
    Qed.

    Theorem add_add :
      forall a v1 v2 m,
        add a v1 (add a v2 m) = add a v1 m.
    Proof.
      intros.
      apply mapsto_extensionality; intuition idtac.
      - destruct (cmp_dec x a); fwd.
      - destruct (cmp_dec x a); fwd.
    Qed.

    Lemma cmp_lt_neq1 : forall a1 a2,
        cmp a1 a2 = Gt ->
        a1 <> a2.
    Proof.
      intros.
      destruct (cmp_dec a1 a2); subst; auto.
      rewrite cmp_refl in *; congruence.
    Qed.

    Lemma cmp_lt_neq2 : forall a1 a2,
        cmp a1 a2 = Lt ->
        a1 <> a2.
    Proof.
      intros.
      destruct (cmp_dec a1 a2); subst; auto.
    Qed.

    Hint Resolve cmp_lt_neq1 cmp_lt_neq2.

    Theorem add_remove_ne :
      forall a1 v1 a2 m,
        a1 <> a2 ->
        add a1 v1 (remove a2 m) = remove a2 (add a1 v1 m).
    Proof.
      intros.
      apply mapsto_extensionality; intuition idtac.
      - destruct (cmp_dec x a1); fwd.
      - fwd.
        destruct (cmp_dec x a1); fwd.
    Qed.

    Theorem remove_remove :
      forall a1 a2 m,
        remove a1 (remove a2 m) = remove a2 (remove a1 m).
    Proof.
      intros.
      apply mapsto_extensionality; intuition idtac.
      - fwd.
      - fwd.
    Qed.

    Theorem remove_add :
      forall a1 v1 m,
        ~ In a1 m ->
        remove a1 (add a1 v1 m) = m.
    Proof.
      intros.
      apply mapsto_extensionality; intuition idtac.
      - fwd.
      - destruct (cmp_dec x a1); subst.
        apply mapsto_in in H0; eauto.
        fwd.
    Qed.

    Theorem mapsto_remove_ne :
      forall a1 v1 a2 m,
        MapsTo a1 v1 m ->
        a1 <> a2 ->
        MapsTo a1 v1 (remove a2 m).
    Proof.
      intros.
      apply remove_mapsto; auto.
    Qed.

    Theorem mapsto_add :
      forall a1 v1 v1' m,
        MapsTo a1 v1 (add a1 v1' m) ->
        v1 = v1'.
    Proof.
      intros.
      apply mapsto_add_eq in H; auto.
    Qed.

    Theorem mapsto_add_nilpotent :
      forall a v m,
        MapsTo a v m ->
        add a v m = m.
    Proof.
      intros.
      apply mapsto_extensionality; intuition idtac.
      - destruct (cmp_dec x a); fwd.
      - destruct (cmp_dec x a); fwd.
        replace v0 with v in * by ( eapply mapsto_unique; eauto ).
        fwd.
    Qed.

    Definition is_permutation_key (l : list A) (m : t) : Prop :=
      forall x, List.In x l <-> In x m.

    Definition is_permutation_val (l : list V) (m : t) : Prop :=
      forall x, List.In x l <-> (exists k, MapsTo k x m).

    Theorem is_permutation_in :
      forall k kl m,
        is_permutation_key kl m ->
        List.In k kl ->
        In k m.
    Proof.
      firstorder.
    Qed.

    Theorem is_permutation_in' :
      forall k kl m,
        is_permutation_key kl m ->
        In k m ->
        List.In k kl.
    Proof.
      firstorder.
    Qed.

    Theorem in_elements_mapsto :
      forall k v m,
        List.In (k, v) (elements m) ->
        MapsTo k v m.
    Proof.
      firstorder.
    Qed.

    Theorem is_permutation_key_to_val:
      forall m kl vl,
        is_permutation_key kl m ->
        Forall2 (fun k v => MapsTo k v m) kl vl ->
        is_permutation_val vl m.
    Proof.
      unfold is_permutation_key.
      unfold is_permutation_val.
      split; intros.
      - eapply in_split in H1.
        destruct H1. destruct H1. subst.
        eapply Forall2_app_inv_r in H0.
        destruct H0. destruct H0. intuition subst.
        inversion H0; clear H0; subst.
        eauto.
      - destruct H1.
        eapply mapsto_in in H1 as H1'.
        eapply H in H1'; clear H.
        eapply in_split in H1'.
        destruct H1'. destruct H. subst.
        eapply Forall2_app_inv_l in H0.
        destruct H0. destruct H. intuition subst.
        inversion H; clear H; subst.
        eapply mapsto_unique in H1; eauto; subst.
        eapply in_or_app; right.
        constructor; eauto.
    Qed.

    Definition is_permutation_kv (l : list (A*V)) (m : t) : Prop :=
      forall k v,
        List.In (k, v) l <-> MapsTo k v m.

    Theorem is_permutation_key_to_kv:
      forall m kvl,
        is_permutation_key (map fst kvl) m ->
        Forall (fun '(k, v) => MapsTo k v m) kvl ->
        is_permutation_kv kvl m.
    Proof.
      unfold is_permutation_key.
      unfold is_permutation_kv.
      split; intros.
      - eapply Forall_forall in H0; eauto.
        simpl in *; eauto.
      - eapply mapsto_in in H1 as H1'.
        eapply H in H1'.
        eapply in_map_iff in H1'; destruct H1'.
        intuition subst.
        eapply Forall_forall in H0; eauto.
        destruct x; simpl in *.
        eapply mapsto_unique in H1; eauto.
        subst; eauto.
    Qed.

   Definition is_permutation (T:Type) (l1 : list T) (l2: list T) : Prop :=
      forall x, List.In x l1 <-> List.In x l2.

   Lemma permutation_val_is_permutation:  forall (l1: list V)  (l2: list V)  (m : t),
      is_permutation_val l1 m ->
      is_permutation_val l2 m ->
      is_permutation l1 l2.
   Proof.
     intros.
     unfold is_permutation_val in *.
     unfold is_permutation in *.
     intros; split; intros.
     - specialize (H x).
       destruct H; auto.
       specialize (H H1).
       specialize (H2 H).
       specialize (H0 x).
       destruct H0; auto.
     - specialize (H0 x).
       destruct H0; auto.
       specialize (H0 H1).
       specialize (H x).
       destruct H; auto.
   Qed.

   Lemma permutation_is_permutation_val : forall (l1: list V)  (l2: list V)  (m : t),
       is_permutation l2 l1 ->
       is_permutation_val l2 m ->
       is_permutation_val l1 m.
   Proof.
     firstorder.
   Qed.

   Lemma is_permutation_val_add: forall k v (l:list V) (m:t),
       ~ In k m ->
       is_permutation_val l m ->
       is_permutation_val (v::l) (add k v m).
   Proof.
     intros.
     unfold is_permutation_val.
     intros; split; intro.
     - apply in_inv in H1. intuition; subst.
       + eexists k.
         apply add_mapsto.
       + unfold is_permutation_val in *.
         specialize (H0 x).
         destruct H0.
         specialize (H0 H2).
         destruct H0.
         exists x0.
         eapply mapsto_add_ne'; eauto.
         intro; subst.
         apply mapsto_in in H0; congruence.
     - destruct H1.
       replace (v::l) with ([v]++l) by auto.
       destruct (cmp_dec x0 k); subst.
       + apply mapsto_add_eq in H1; subst.
         apply in_eq; auto.
         auto.
       + apply mapsto_add_ne in H1; subst; auto.
         apply in_or_app; auto.
         right.
            unfold is_permutation_val in *.
            specialize (H0 x).
            destruct H0.
            apply H2.
            exists x0; auto.
   Qed.

   Lemma in_keys: forall k (m:t),
       In k m ->
       List.In k (keys m).
   Proof.
     intros.
     unfold keys.
     apply in_mapsto_exists in H.
     destruct H.
     unfold MapsTo in *.
     replace k with (fst (k, x)) by auto.
     eapply in_map; auto.
   Qed.

   Lemma keys_in: forall k (m:t),
       List.In k (keys m) ->
       In k m.
   Proof.
     intros.
     unfold keys in *.
     eapply in_map_iff in H.
     destruct H.
     intuition.
     destruct x.
     eapply in_elements_mapsto in H1; simpl in *; subst.
     apply mapsto_in in H1; auto.
   Qed.

   Lemma in_keys_add_eq: forall k v (m:t),
       List.In k (keys (add k v m)).
   Proof.
     intros.
     assert (In k (add k v m)).
     apply add_in.
     apply in_keys; auto.
   Qed.

   Lemma in_keys_add: forall k1 k2 v (m:t),
       List.In k1 (keys m) ->
       List.In k1 (keys (add k2 v m)).
   Proof.
     intros.
     assert (In k1 m).
     apply keys_in; auto.
     eapply in_add with (a2 := k2) (v := v) in H0.
     apply in_keys in H0; auto.
   Qed.

   Lemma in_add_or: forall k1 k2 v (m:t),
       List.In k1 (keys (add k2 v m)) ->
       k1 = k2 \/ List.In k1 (keys m).
   Proof.
     intros.
     unfold keys in *.
     destruct (cmp_dec k1 k2); auto.
     right.
     eapply in_map_iff in H.
     destruct H.
     destruct x.
     intuition.
     eapply in_map_iff.
     exists (a, v0).
     split; auto.
     apply in_elements_mapsto in H1.
     apply mapsto_add_ne in H1; auto.
     intro. subst. simpl in *. congruence.
   Qed.

   Lemma is_permutation_cons_add_key: forall (k:A) (v:V) (m:t),
       is_permutation (k :: (keys m)) (keys (add k v m)).
   Proof.
     intros.
     unfold is_permutation.
     intro. split; intro.
     - destruct (cmp_dec x k); subst.
       apply in_keys_add_eq.
       apply in_keys_add.
       apply in_inv in H; auto.
       intuition; auto.
     - apply in_add_or in H.
       intuition; subst.
       apply in_eq.
    Qed.

  End Maps.

  Arguments t A V {Acmp}.
  Arguments empty {A} {V} {Acmp}.

  Section MapKeys.

    Variable A1:Type.
    Variable A2:Type.
    Variable V:Type.
    Context {A1cmp: Ordering A1}.
    Context {A2cmp: Ordering A2}.

    Variable f : A1 -> A2.

    Fixpoint insert_f (l : list (A1*V)) (m : t A2 V) : t A2 V :=
      match l with
      | nil => m
      | (a1, v) :: l' =>
        add (f a1) v (insert_f l' m)
      end.

    Definition map_keys (m1 : t A1 V) : t A2 V :=
      insert_f (elements m1) empty.

    Theorem map_keys_in : forall k m,
      In k m ->
      In (f k) (map_keys m).
    Proof.
      destruct m.
      unfold map_keys; simpl.
      unfold In at 1; unfold keys; simpl.
      clear.
      induction elements0; simpl; intros; eauto.
      intuition; subst.
      - destruct a; simpl.
        eapply add_in.
      - eapply in_add; eauto.
    Qed.

    Theorem map_keys_in' : forall k m,
      In k (map_keys m) ->
        exists k',
          In k' m /\
          k = f k'.
    Proof.
      destruct m.
      unfold map_keys; simpl.
      unfold In at 2; unfold keys; simpl.
      clear.
      induction elements0; simpl; intros; eauto.
      - inversion H.
      - destruct a.
        eapply add_in' in H.
        intuition; subst; eauto.
        destruct H; intuition eauto.
    Qed.

    Definition injective :=
      forall k1 k2,
        k1 <> k2 ->
        f k1 <> f k2.

    Theorem map_keys_mapsto : forall k v m,
      injective ->
      MapsTo k v m ->
      MapsTo (f k) v (map_keys m).
    Proof.
      destruct m.
      intro.
      unfold map_keys; simpl.
      unfold MapsTo at 1; simpl.
      subst keys0.
      induction elements0; simpl; intros; eauto.
      intuition; subst.
      - eapply add_mapsto.
      - destruct a.
        eapply mapsto_add_ne'.
        + eapply IHelements0; eauto.
          inversion elem_sorted0; eauto.
        + clear IHelements0.
          eapply H; clear H.
          eapply in_split in H1.
          destruct H1. destruct H. subst.
          simpl in *.
          rewrite map_app in *.
          simpl in *.
          assert (a <> k); eauto.
          eapply sorted_distinct; eauto.
    Qed.

    Theorem map_keys_mapsto' : forall k v m,
      MapsTo k v (map_keys m) ->
        exists k',
          MapsTo k' v m /\
          k = f k'.
    Proof.
      destruct m.
      unfold map_keys; simpl.
      unfold MapsTo at 2; simpl.
      subst keys0.
      induction elements0; simpl; intros; eauto.
      - inversion H.
      - destruct a.
        eapply mapsto_add_or in H.
        intuition; subst; eauto.
        edestruct IHelements0; eauto.
        inversion elem_sorted0; eauto.
        intuition eauto.
    Qed.

    Theorem map_keys_add : forall k v m,
      injective ->
      map_keys (add k v m) = add (f k) v (map_keys m).
    Proof.
      destruct m; intros.
      unfold map_keys. simpl.
      subst keys0.
      induction elements0; simpl; intros; eauto.
      destruct a.
      inversion elem_sorted0; clear elem_sorted0; subst.
      intuition idtac.
      destruct (cmp k a) eqn:He.
      - apply cmp_eq in He; subst.
        rewrite add_add.
        reflexivity.
      - reflexivity.
      - simpl.
        rewrite add_add_ne. f_equal.
        eauto.
        eapply cmp_lt_neq1 in He.
        eapply H; eauto.
    Qed.

    Theorem map_keys_remove : forall k m,
      injective ->
      map_keys (remove k m) = remove (f k) (map_keys m).
    Proof.
      destruct m; intros.
      unfold map_keys. simpl.
      subst keys0.
      induction elements0; simpl; intros; eauto.
      + eapply elements_eq; simpl. eauto.
      + destruct a.
        inversion elem_sorted0; clear elem_sorted0; subst.
        intuition idtac.
        destruct (cmp k a) eqn:He; simpl.
        - apply cmp_eq in He; subst.
          rewrite remove_add.
          reflexivity.

          clear H3. clear H0.
          induction elements0; simpl; eauto.
          inversion H2; clear H2; intuition subst.
          eapply H5; clear H5.
          destruct a0; simpl in *.
          eapply cmp_lt_neq2 in H3.
          eapply in_add_ne in H2; eauto.

        - eapply cmp_lt_neq2 in He as He'.
          assert (f k <> f a) by firstorder.
          rewrite <- add_remove_ne; eauto.
          rewrite <- H0; clear H0.
          f_equal. f_equal.

          clear H3. clear H1. clear He'. clear H. clear f.
          induction elements0; simpl; eauto.
          inversion H2; clear H2; subst; intuition idtac.
          destruct a0.
          unfold cmp_lt in H1; simpl in *.
          eapply cmp_trans in H1; eauto.
          destruct (cmp k a0) eqn:He'; congruence.

        - eapply cmp_lt_neq1 in He.
          assert (f k <> f a) by firstorder.
          rewrite <- add_remove_ne; eauto.
          rewrite <- H0.
          eauto.
    Qed.

  End MapKeys.

End FMap.


Instance cmp_equal_dec : forall {T} {_ : Ordering T}, EqualDec T.
Proof.
  unfold EqualDec; intros.
  destruct (cmp x y) eqn:He.
  eapply cmp_eq1 in He; eauto.
  eapply FMap.cmp_lt_neq2 in He; eauto.
  eapply FMap.cmp_lt_neq1 in He; eauto.
Defined.
