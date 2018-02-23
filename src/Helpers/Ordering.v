Require Import Arith.
Require Import Omega.
Require Import String.
Require List.

Import List.ListNotations.
Open Scope list.

Set Implicit Arguments.

Class Ordering A :=
  { cmp: A -> A -> comparison;
    cmp_eq: forall x y,
        cmp x y = Eq <-> x = y;
    cmp_antisym: forall x y,
        cmp x y = Gt <-> cmp y x = Lt;
    cmp_trans : forall x y z,
        cmp x y = Lt -> cmp y z = Lt ->
        cmp x z = Lt; }.

Lemma cmp_eq1 : forall A (ordA:Ordering A) x y,
    cmp x y = Eq -> x = y.
Proof.
  intros.
  apply cmp_eq; auto.
Qed.

Lemma cmp_refl : forall A (ordA:Ordering A) x,
    cmp x x = Eq.
Proof.
  intros.
  apply cmp_eq; auto.
Qed.

Lemma cmp_antisym1 : forall A (ordA:Ordering A) x y,
    cmp x y = Gt -> cmp y x = Lt.
Proof.
  intros.
  apply cmp_antisym; auto.
Qed.

Lemma cmp_antisym2 : forall A (ordA:Ordering A) x y,
    cmp x y = Lt -> cmp y x = Gt.
Proof.
  intros.
  apply cmp_antisym; auto.
Qed.

Hint Resolve cmp_eq1 cmp_refl cmp_antisym1 cmp_antisym2 cmp_trans.

Definition cmp_lt {A} `{Ordering A} :=
  fun x y => cmp x y = Lt.

Definition cmp_dec {A} `{Ordering A} : forall (x y:A), {x=y} + {x<>y}.
Proof.
  intros.
  destruct_with_eqn (cmp x y).
  left; eauto.
  right; intro.
  apply cmp_eq in H0; congruence.
  right; intro.
  apply cmp_eq in H0; congruence.
Defined.

Definition ord_spec {A} `{Ordering A} :
  forall x y, CompareSpec (x=y) (cmp x y = Lt /\ cmp y x = Gt) (cmp y x = Lt /\ cmp x y = Gt) (cmp x y).
Proof.
  intros.
  destruct_with_eqn (cmp x y);
    constructor;
    intuition eauto.
Defined.

Instance nat_Ordering : Ordering nat.
Proof.
  refine {| cmp := fun x y =>
                     if Nat.eq_dec x y then Eq
                     else if lt_dec x y then Lt
                          else Gt; |};
    intros.
  - destruct (Nat.eq_dec x y); split; intros;
      subst; try congruence.
    destruct (lt_dec x y); congruence.
  - destruct (Nat.eq_dec x y), (Nat.eq_dec y x);
      subst;
      try congruence.
    split; congruence.
    destruct (lt_dec x y), (lt_dec y x);
      try omega.
    split; congruence.
    split; auto.
  - destruct (Nat.eq_dec x y), (Nat.eq_dec y z), (Nat.eq_dec x z);
      subst;
      try congruence.
    destruct (lt_dec z y), (lt_dec y z);
      try congruence;
      try omega.
    destruct (lt_dec x y), (lt_dec y z), (lt_dec x z);
      try congruence;
      try omega.
Defined.

Instance prod_Ordering A B {ordA:Ordering A} {ordB: Ordering B} : Ordering (A*B).
Proof.
  refine {| cmp := fun '(x1, x2) '(y1, y2) =>
                     match cmp x1 y1 with
                     | Lt => Lt
                     | Gt => Gt
                     | Eq => cmp x2 y2
                     end |}; intros.
  - destruct x, y.
    destruct (ord_spec a a0); subst; (intuition eauto);
      repeat match goal with
             | [ H: cmp _ _ = Eq |- _ ] =>
               apply cmp_eq in H
             | [ H: (_, _) = (_, _) |- _ ] =>
               inversion H; clear H
             end; subst;
        try congruence; eauto.
  - destruct x, y.
    destruct (ord_spec a a0); subst.
    * rewrite cmp_refl.
      intuition eauto.
    * destruct H.
      rewrite H0.
      split; congruence.
    * intuition.
      rewrite H0; auto.
  - destruct x, y, z.
    destruct (ord_spec a a0), (ord_spec a0 a1);
      intuition subst;
      rewrite ?cmp_refl in *;
      repeat match goal with
             | [ H: cmp _ _ = _ |- _ ] =>
               rewrite H in *
             end;
      try congruence;
      eauto.
    erewrite cmp_trans; eauto.
Defined.

Instance sum_Ordering A B : forall (ordA:Ordering A) (ordB:Ordering B), Ordering (A+B).
Proof.
  intros.
  refine {| cmp := fun x y =>
                     match x, y with
                     | inl x, inl y => cmp x y
                     | inr x, inr y => cmp x y
                     | inl _, inr _ => Lt
                     | inr _, inl _ => Gt
                     end; |}; intros.
  - destruct x, y; (intuition eauto);
      repeat match goal with
             | [ H: inl _ = inl _ |- _ ] =>
               inversion H; subst; clear H
             | [ H: inr _ = inr _ |- _ ] =>
               inversion H; subst; clear H
             | [ H: cmp _ _ = Eq |- _ ] =>
               apply cmp_eq in H; subst
             end;
      try congruence;
      eauto.
  - destruct x, y; intuition eauto.
  - destruct x, y, z; (intuition eauto);
      try congruence.
Defined.

Record injection A B :=
  { inject: A -> B;
    inject_ok : forall x y, inject x = inject y -> x = y; }.

Theorem injection_Ordering A {B} : forall (ordA:Ordering A) (inj:injection B A), Ordering B.
Proof.
  intros.
  refine {| cmp := fun x y =>
                     cmp (inject inj x) (inject inj y) |}; intuition eauto.
  eapply inject_ok; eauto.
  subst; rewrite cmp_refl; auto.
Defined.

Arguments injection_Ordering A {B} ordA inj.

Fixpoint cmp_list A (ord:Ordering A) (l1 l2:list A) : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _::_ => Lt
  | _::_, [] => Gt
  | x::xs, y::ys => match cmp x y with
                   | Eq => cmp_list ord xs ys
                   | Lt => Lt
                   | Gt => Gt
                   end
  end.

Section TwoListInduction.

  Variable A:Type.
  Variable B:Type.
  Variable P: list A -> list B -> Prop.

  Fixpoint zip (l1: list A) (l2:list B) : list (A*B) :=
    match l1 with
    | nil => nil
    | x::xs => match l2 with
              | nil => nil
              | y::ys => (x,y)::zip xs ys
              end
    end.


  Hypothesis Pnil_nil : P [] [].
  Hypothesis Pnil_cons : forall y ys, P [] (y::ys).
  Hypothesis Pcons_nil : forall x xs, P (x::xs) [].

  Theorem empty_zip : forall l1 l2,
      zip l1 l2 = [] ->
      P l1 l2.
  Proof.
    induction l1; simpl; intros.
    destruct l2; eauto.
    destruct l2; simpl in *; try congruence; eauto.
  Qed.

  Hypothesis Pind : forall x y xs ys,
      P xs ys ->
      P (x::xs) (y::ys).

  Theorem two_list_induction : forall l1 l2,
      P l1 l2.
  Proof.
    intros.
    remember (zip l1 l2).
    generalize dependent l2.
    generalize dependent l1.
    induction l; simpl; intros.
    - apply empty_zip; auto.
    - destruct l1, l2; simpl in *; try congruence.
      inversion Heql; subst.
      specialize (IHl l1 l2); intuition.
  Qed.

End TwoListInduction.

Section ThreeListInduction.

  Variable A:Type.
  Variable B:Type.
  Variable C:Type.

  Fixpoint zip3 (l1: list A) (l2:list B) (l3:list C) : list (A*B*C) :=
    zip (zip l1 l2) l3.

  Variable P: list A -> list B -> list C -> Prop.

  Hypothesis Psome_nil : forall xs ys zs,
      xs = [] \/ ys = [] \/ zs = [] -> P xs ys zs.

  Hypothesis Pind : forall x y z xs ys zs,
      P xs ys zs ->
      P (x::xs) (y::ys) (z::zs).

  Theorem three_list_induction : forall l1 l2 l3,
      P l1 l2 l3.
  Proof.
    intros.
    remember (zip l1 l2).
    generalize dependent l2.
    generalize dependent l1.
    eapply two_list_induction with (l1 := l) (l2 := l3);
      intros; eauto.
    destruct l1, l2; eauto.
    simpl in *; congruence.

    generalize dependent H.
    generalize dependent Heql.
    generalize dependent ys.
    generalize dependent xs.
    generalize dependent x.
    generalize dependent y.
    clear l.
    clear l3.
    eapply two_list_induction with (l1:=l1) (l2:=l2); simpl; intros; eauto.

    inversion Heql; subst; clear Heql.
    eauto.
  Qed.

End ThreeListInduction.

Instance list_Ordering A {ord:Ordering A} : Ordering (list A).
Proof.
  refine {| cmp := cmp_list ord |}; intros.
  - eapply two_list_induction with (l1 := x) (l2 := y);
      simpl in *;
      try solve [ (intuition eauto); congruence ];
      intros.
    destruct H.
    destruct (ord_spec x0 y0); (intuition subst); eauto; try congruence.
    inversion H2; subst; clear H2; intuition eauto.
  - eapply two_list_induction with (l1 := x) (l2 := y);
      simpl in *;
      try solve [ (intuition eauto); congruence ];
      intros.
    destruct (ord_spec x0 y0); (intuition subst); eauto; try congruence.
    rewrite cmp_refl; eauto.
    rewrite cmp_refl in *; eauto.
    rewrite H2 in *; congruence.
    rewrite H1; eauto.
  - generalize dependent H.
    generalize dependent H0.
    eapply three_list_induction with (l1:=x) (l2:=y) (l3:=z); intros; simpl.
    intuition subst.
    destruct ys, zs; simpl in *; try congruence.
    destruct xs, zs; simpl in *; try congruence.
    destruct xs, ys; simpl in *; try congruence.
    simpl in *.
    destruct (ord_spec y0 z0), (ord_spec x0 y0); subst; eauto;
      intuition eauto;
      repeat match goal with
             | [ H: context[cmp ?x ?x] |- _ ] =>
               rewrite cmp_refl in H
             | [ |- context[cmp ?x ?x] ] =>
               rewrite cmp_refl
             | [ H: context[cmp ?x ?y], Heq: cmp ?x ?y = _ |- _ ] =>
               rewrite Heq in H
             | [ Heq: cmp ?x ?y = _ |- context[cmp ?x ?y] ] =>
               rewrite Heq
             | _ =>
               try erewrite cmp_trans by eauto
             end;
      eauto;
      try congruence.
Defined.

Instance bool_Ordering : Ordering bool.
Proof.
  refine {| cmp := fun x y =>
                     match x, y with
                     | false, false => Eq
                     | true, true => Eq
                     | false, true => Lt
                     | true, false => Gt
                     end |}; intros.
  destruct x, y; simpl; (intuition idtac); congruence.
  destruct x, y; simpl; (intuition idtac); congruence.
  destruct x, y, z; simpl; (intuition idtac); congruence.
Defined.

Instance ascii_Ordering : Ordering Ascii.ascii.
Proof.
  apply (injection_Ordering (bool*bool*bool*bool*bool*bool*bool*bool)%type).
  typeclasses eauto.

  unshelve econstructor; intros.
  destruct H.
  exact (b, b0, b1, b2, b3, b4, b5, b6).
  destruct x, y.
  congruence.
Defined.

Fixpoint string_to_list (s:string) : list Ascii.ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: string_to_list s
  end.

Instance string_Ordering : Ordering string.
Proof.
  apply (injection_Ordering (list Ascii.ascii)).
  typeclasses eauto.
  refine {| inject := string_to_list |}; intros.
  remember (string_to_list x).
  remember (string_to_list y).
  generalize dependent x.
  generalize dependent y.
  generalize dependent H.
  eapply two_list_induction with (l1 := l) (l2 := l0); intros;
    try congruence.
  destruct x, y; simpl in *; try congruence.
  inversion H0; subst; clear H0; intuition.
  destruct x0, y0; simpl in *; try congruence.
  inversion Heql0; subst; clear Heql0.
  inversion Heql; subst; clear Heql.
  f_equal.
  eapply H0; eauto.
Defined.

Inductive sorted A (lt: A -> A -> Prop) : list A -> Prop :=
| sorted_nil : sorted lt nil
| sorted_cons : forall x l,
    List.Forall (lt x) l ->
    sorted lt l ->
    sorted lt (x::l).
