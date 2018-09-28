Require Import Morphisms.
Require Import Helpers.Setoid.
Require PeanoNat.
Require List.

Require Import Helpers.ProofAutomation.Propositional.

Set Implicit Arguments.

Generalizable Variables A.

Class Monoid_Ops (A:Setoid) :=
  { dot : A -> A -> A;
    one : A; }.

Infix "⋅" := dot (at level 40, left associativity).
Notation "1" := one.

Class SemiLattice_Ops (A:Setoid) :=
  { plus: A -> A -> A;
    zero: A }.

Infix "+" := plus.
Notation "0" := zero.

Class Star_Op (A:Setoid) :=
  { star: A -> A; }.

Notation "x *" := (star x) (at level 0, format "'[' x ']' *").

Definition le `{_: SemiLattice_Ops A} (x y:A) := x + y == y.

Infix "<=" := le.

Section Laws.
  Context {A} {Mo: Monoid_Ops A} {SLo: SemiLattice_Ops A} {Ko: Star_Op A}.

  Class Monoid :=
    { dot_compat :> Proper (equiv ==> equiv ==> equiv) dot;
      dot_assoc : forall x y z, x ⋅ (y ⋅ z) == x ⋅ y ⋅ z;
      dot_neutral_left : forall x, 1 ⋅ x == x;
      dot_neutral_right : forall x, x ⋅ 1 == x }.

  Class SemiLattice :=
    { plus_compat :> Proper (equiv ==> equiv ==> equiv) plus;
      plus_neutral_left : forall x, 0 + x == x;
      plus_idem : forall x, x + x == x;
      plus_assoc : forall x y z, x + (y + z) == x + y + z;
      plus_comm : forall x y, x + y == y + x; }.

  Class IdemSemiRing :=
    { Monoid_ :> Monoid;
      SemiLattice_ :> SemiLattice;
      dot_ann_left : forall x, 0 ⋅ x == 0;
      dot_ann_right : forall x, x ⋅ 0 == 0;
      dot_distr_right : forall x y z, (x + y) ⋅ z == x ⋅ z + y ⋅ z;
      dot_distr_left : forall x y z, z ⋅ (x + y) == z ⋅ x + z ⋅ y; }.

  Class KleeneAlgebra :=
    { IdemSemiRing_ :> IdemSemiRing;
      star_one_l : forall p, 1 + p ⋅ p* <= p*;
      star_one_r : forall p, 1 + p* ⋅ p <= p*;
      star_ind_l : forall p q x, q + p ⋅ x <= x -> p* ⋅ q <= x;
      star_ind_r : forall p q x, q + x ⋅ p <= x -> q ⋅ p* <= x; }.

End Laws.

Section Theorems.
  Context A {Mo: Monoid_Ops A} {SLo: SemiLattice_Ops A} {Ko: Star_Op A}.
  Context {M: Monoid}.
  Context {SL: SemiLattice}.
  Context {ISL: IdemSemiRing}.
  Context {KA: KleeneAlgebra}.

  Theorem le_eq : forall p q, p <= q ->
                          q <= p ->
                          p == q.
  Proof.
    unfold le; intros.
    rewrite <- H.
    rewrite <- H0 at 1.
    apply plus_comm.
  Qed.

  Hint Rewrite plus_idem : ka.
  Hint Rewrite plus_assoc : ka.
  Hint Rewrite dot_assoc : ka.
  Hint Rewrite plus_neutral_left : ka.

  Lemma plus_neutral_right : forall x, x + 0 == x.
  Proof.
    intros.
    rewrite plus_comm.
    apply plus_neutral_left.
  Qed.

  Hint Rewrite plus_neutral_right : ka.

  Hint Rewrite dot_ann_left dot_ann_right dot_neutral_left dot_neutral_right : ka.

  Ltac is_removed x :=
    lazymatch goal with
    | [ H: context[x] |- _ ] => fail
    | [ |- context[x] ] => fail
    | _ => idtac
    end.

  Ltac does_not_appear_in x e :=
    lazymatch e with
    | context[x] => fail
    | _ => idtac
    end.

  Hint Rewrite dot_distr_right dot_distr_left : ka_distr.

  Ltac equiv_subst :=
    match goal with
    | [ H: ?v == ?repl |- _ ] =>
      is_var v;
      does_not_appear_in v repl;
      rewrite H in *;
      try (clear H; is_removed v)
    | [ H: ?repl == ?v |- _ ] =>
      is_var v;
      does_not_appear_in v repl;
      rewrite <- H in *;
      try (clear H; is_removed v)
    | |- ?x == ?x => reflexivity
    | [ |- _ ] => progress autorewrite with ka in *
    end.

  Ltac cleanup :=
    intros;
    autorewrite with ka;
    repeat (equiv_subst || autorewrite with ka in *);
            trivial.


  Ltac cleanup_distr :=
    intros;
    autorewrite with ka ka_distr;
    repeat (equiv_subst || autorewrite with ka ka_distr in *);
            trivial.

  Hint Resolve plus_idem le_eq.
  Hint Resolve (reflexivity : forall x, x == x).

  Instance le_PreOrder : PreOrder le.
  Proof.
    unfold le.
    constructor; hnf; intros.
    - rewrite plus_idem; auto.
    - rewrite <- H0.
      rewrite <- H at 2.
      cleanup.
  Qed.

  Instance le_PartialOrder : PartialOrder equiv le.
  Proof.
    unfold le.
    constructor; repeat (hnf; intros); unfold Basics.flip in *.
    - unfold le.
      cleanup; eauto.
    - hnf in H; propositional; auto.
  Qed.

  Hint Unfold Proper respectful Basics.flip Basics.impl : m.

  Lemma abc_to_acb : forall a b c,
      a + b + c == a + c + b.
  Proof.
    intros.
    rewrite <- plus_assoc.
    rewrite (plus_comm b c).
    cleanup.
  Qed.

  Instance le_plus_respectful :
    Proper (le ==> le ==> le) plus.
  Proof.
    autounfold with m; unfold le; intros.
    cleanup.
    rewrite (abc_to_acb x x0 y).
    rewrite H.
    rewrite <- plus_assoc.
    rewrite H0.
    auto.
  Qed.

  Instance le_star_sub : subrelation equiv le.
  Proof.
    hnf; intros.
    unfold le; cleanup.
  Qed.

  Lemma distr_abcd : forall a b c d,
      (a + b) ⋅ (c + d) ==
      a ⋅ c + b ⋅ d + (a ⋅ d + b ⋅ c).
  Proof.
    intros.
    rewrite ?dot_distr_left, ?dot_distr_right.
    generalize dependent (a⋅c); intro w.
    generalize dependent (b⋅c); intro x.
    generalize dependent (a⋅d); intro y.
    generalize dependent (b⋅d); intro z.
    rewrite (plus_comm y z).
    rewrite plus_assoc at 1.
    rewrite (abc_to_acb w x z).
    rewrite (plus_comm y x).
    cleanup.
  Qed.

  Instance le_dot_respectful :
      Proper (le ==> le ==> le) dot.
  Proof.
    autounfold with m; intros.
    unfold le in *.

    assert ((x + y) ⋅ (x0 + y0) == y ⋅ y0).
    rewrite H, H0; auto.
    rewrite <- H1 at 2.

    rewrite distr_abcd.
    rewrite <- (plus_idem (x ⋅ x0 + y ⋅ y0)) at 2.
    rewrite <- plus_assoc.

    assert (x ⋅ x0 + y ⋅ y0 + (x ⋅ y0 + y ⋅ x0) ==
            (x + y) ⋅ (x0 + y0)).
    rewrite abc_to_acb.
    rewrite ?dot_distr_left, ?dot_distr_right; cleanup.
    rewrite (abc_to_acb (x⋅x0) (x⋅y0) (y⋅x0)).
    auto.

    rewrite H2.
    rewrite H1.
    rewrite <- plus_assoc.
    rewrite plus_idem.
    auto.
  Qed.

  Theorem plus_r_monotone : forall r p q,
      p <= q ->
      p + r <= q + r.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Theorem plus_l_monotone : forall r p q,
      p <= q ->
      r + p <= r + q.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Theorem dot_r_monotone : forall r p q,
      p <= q ->
      p ⋅ r <= q ⋅ r.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Theorem dot_l_monotone : forall r p q,
      p <= q ->
      r ⋅ p <= r ⋅ q.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Instance equiv_impl_le :
    Proper (equiv ==> equiv ==> Basics.impl) le.
  Proof.
    autounfold with m; unfold le; intros.
    cleanup.
  Qed.

  Theorem star_ind1_l : forall p x, 1 + p ⋅ x <= x -> p* <= x.
  Proof.
    intros.
    eapply star_ind_l in H.
    cleanup; auto.
  Qed.

  Theorem star_ind1_r : forall p x, 1 + x ⋅ p <= x -> p* <= x.
  Proof.
    intros.
    eapply star_ind_r in H.
    cleanup.
  Qed.

  Theorem star_and : forall p q,
      q + p⋅p* ⋅ q <= p* ⋅ q.
  Proof.
    intros.
    pose proof (star_one_l p).
    apply (dot_r_monotone q) in H.
    cleanup_distr.
  Qed.

  Theorem le_star_respectful :
    Proper (le ==> le) star.
  Proof.
    autounfold with m; intros.
    apply star_ind1_l.
    etransitivity; [ | apply star_one_l ].
    rewrite H; reflexivity.
  Qed.

  Theorem le_0 : forall x,
      0 <= x.
  Proof.
    unfold le; cleanup.
  Qed.

  Hint Immediate le_0.

  Theorem plus_le_r : forall p q,
      p <= p + q.
  Proof.
    intros.
    unfold le; cleanup.
  Qed.

  Theorem plus_le_l : forall p q,
      p <= q + p.
  Proof.
    intros.
    rewrite plus_comm.
    apply plus_le_r.
  Qed.

  Hint Resolve (reflexivity : forall p, p <= p).

  Ltac monotonicity :=
    match goal with
    | [ |- ?x ⋅ _ <= ?x ⋅ _ ] =>
      apply dot_l_monotone
    | [ |- _ ⋅ ?y <= _ ⋅ ?y ] =>
      apply dot_r_monotone
    | [ |- ?x + _ <= ?x + _ ] =>
      apply plus_l_monotone
    | [ |- _ + ?y <= _ + ?y ] =>
      apply plus_r_monotone
    | [ |- ?x + _ == ?x + _ ] =>
      apply plus_compat; [ reflexivity | ]
    | [ |- _ + ?y == _ + ?y ] =>
      apply plus_compat; [ | reflexivity ]
    | [ |- ?p <= ?p + _ ] =>
      apply plus_le_r
    | [ |- ?p <= _ + ?p ] =>
      apply plus_le_l
    end.

  Lemma plus_split : forall p q x,
      p <= x ->
      q <= x ->
      p + q <= x.
  Proof.
    unfold le; intros.
    rewrite <- plus_assoc.
    rewrite H0.
    auto.
  Qed.

  Theorem star_expand p :
      p* == 1 + p ⋅ p*.
  Proof.
    apply le_eq; [ | apply star_one_l ].
    apply star_ind1_l; cleanup.
    repeat monotonicity.
    apply star_one_l.
  Qed.

  Theorem star_expand_l p :
      p* == 1 + p* ⋅ p.
  Proof.
    apply le_eq; [ | apply star_one_r ].
    apply star_ind1_r; cleanup.
    repeat monotonicity.
    apply star_one_r.
  Qed.

  Lemma star_one_le_l p :
      p ⋅ p* <= p*.
  Proof.
    unfold le; intros.
    rewrite star_expand at 2 3.
    cleanup.
    rewrite abc_to_acb.
    cleanup.
    rewrite plus_comm; auto.
  Qed.

  Theorem star_incl_skip p :
    1 <= p*.
  Proof.
    intros.
    rewrite star_expand.
    monotonicity.
  Qed.

  Theorem star_expand1 p : p* == 1 + p*.
  Proof.
    apply le_eq.
    - rewrite star_expand at 1.
      monotonicity.
      apply star_one_le_l.
    - rewrite (star_incl_skip p); cleanup.
  Qed.

  Lemma star_one_le_r p :
      p* ⋅ p <= p*.
  Proof.
    unfold le; intros.
    rewrite star_expand_l at 2 3.
    cleanup.
    rewrite abc_to_acb.
    cleanup.
    rewrite plus_comm; auto.
  Qed.

  Hint Resolve star_one_le_l star_one_le_r.

  Theorem star_one_comm p : p ⋅ p* == p* ⋅ p.
  Proof.
    apply le_eq.
    - apply star_ind_r.
      rewrite star_one_le_r at 1.
      rewrite star_expand1 at 2; cleanup_distr.
    - apply star_ind_l.
      rewrite star_one_le_l at 1.
      rewrite star_expand1 at 2; cleanup_distr.
  Qed.

  Theorem star_square p : p* == p* ⋅ p*.
  Proof.
    apply le_eq.
    - rewrite <- dot_neutral_right at 1.
      monotonicity.
      apply star_incl_skip.
    - apply star_ind_l.
      apply plus_split; auto.
  Qed.

  Theorem star_repeat p : (p*)* == p*.
  Proof.
    apply le_eq.
    - apply star_ind1_l.
      rewrite <- star_square.
      rewrite <- star_expand1; auto.
    - apply le_star_respectful.
      rewrite star_expand.
      rewrite <- star_incl_skip; cleanup.
      monotonicity.
  Qed.

  Lemma quad_product_middle : forall w x y z,
      w ⋅ x ⋅ y ⋅ z == w ⋅ (x ⋅ y) ⋅ z.
  Proof.
    cleanup.
  Qed.

  Theorem sliding p q : (p ⋅ q)* ⋅ p == p ⋅ (q ⋅ p)*.
  Proof.
    apply le_eq.
    - apply star_ind_l; cleanup.
      rewrite quad_product_middle.
      generalize dependent (q ⋅ p); intro y.
      rewrite (star_expand y) at 2; cleanup_distr.
    - apply star_ind_r; cleanup.
      rewrite quad_product_middle.
      generalize dependent (p ⋅ q); intro y.
      rewrite (star_expand_l y) at 2; cleanup_distr.
  Qed.

  Theorem dot_le_star p q r :
    p <= r* ->
    q <= r* ->
    p ⋅ q <= r*.
  Proof.
    intros.
    rewrite H.
    rewrite H0.
    rewrite <- star_square; auto.
  Qed.

  Lemma star_one_iter : forall p,
      p <= p*.
  Proof.
    intros.
    rewrite star_expand.
    rewrite <- star_incl_skip; cleanup.
    monotonicity.
  Qed.

  Theorem star_one_le : forall p q,
      p <= q ->
      p <= q*.
  Proof.
    intros.
    rewrite <- star_one_iter; auto.
  Qed.

  Hint Resolve star_one_le.
  Hint Resolve plus_le_l plus_le_r.

  Theorem denesting p q : (p + q)* == p* ⋅ (q ⋅ p*)*.
  Proof.
    apply le_eq.
    - apply star_ind1_l; cleanup.
      apply plus_split.
      + repeat rewrite <- star_incl_skip at 1; cleanup.
      + cleanup_distr.
        apply plus_split.
        monotonicity; auto.
        rewrite (star_square (q ⋅ _)) at 2; cleanup.
        monotonicity.
        rewrite <- star_incl_skip at 2; cleanup.
        auto.
    - apply star_ind_l.
      apply plus_split.
      + apply star_ind1_l.
        rewrite (star_expand1 (p+q)) at 2.
        monotonicity.
        repeat apply dot_le_star; auto.
        apply le_star_respectful; auto.
      + rewrite (plus_le_r p q) at 1.
        apply star_one_le_l.
  Qed.

  Theorem bisimulation p q r :
    p ⋅ q == q ⋅ r ->
    p* ⋅ q == q ⋅ r*.
  Proof.
    intros.
    apply le_eq.
    - apply star_ind_l; cleanup.
      rewrite H.
      rewrite (star_expand r) at 2; cleanup_distr.
    - apply star_ind_r; cleanup.
      rewrite <- dot_assoc.
      rewrite <- H; cleanup.
      rewrite (star_expand_l p) at 2; cleanup_distr.
  Qed.

  Theorem one_is_zero_star : 0* == 1.
  Proof.
    rewrite star_expand.
    cleanup.
  Qed.

End Theorems.

Import List List.ListNotations.
Open Scope list.

Section ReflTransClosure.

  Context {A:Type}.

  Inductive star_l (l: list A -> Prop) : list A -> Prop :=
  | star_empty : star_l l []
  | star_one_more : forall s s',
      l s ->
      star_l l s' ->
      star_l l (s ++ s').

  Hint Constructors star_l.

  Lemma star_l_one : forall (x:list A -> Prop) s,
      x s ->
      star_l x s.
  Proof.
    intros.
    replace s with (s ++ []); eauto.
    rewrite app_nil_r; auto.
  Qed.

  Hint Resolve star_l_one.

  Inductive star_r (l: list A -> Prop) : list A -> Prop :=
  | star_r_empty : star_r l []
  | star_r_one_more : forall s s',
      star_r l s ->
      l s' ->
      star_r l (s ++ s').

  Hint Constructors star_r.

  Theorem star_r_one : forall (x:list A -> Prop) s,
      x s ->
      star_r x s.
  Proof.
    intros.
    replace s with ([] ++ s); eauto.
  Qed.

  Hint Resolve star_r_one.

  Theorem star_lr : forall l s,
      star_l l s <-> star_r l s.
  Proof.
    split; intros.
    - induction H; eauto.
      clear H0.
      induction IHstar_l; intros;
        rewrite ?app_nil_r, ?app_nil_l;
        eauto.
      rewrite app_assoc.
      eauto.
    - induction H; eauto.
      clear H.
      induction IHstar_r; intros;
        rewrite ?app_nil_r, ?app_nil_l;
        eauto.
      rewrite <- app_assoc.
      eauto.
  Qed.

End ReflTransClosure.

Section LanguageModel.

  Definition language (A:Type) : Setoid.
    refine {| T := list A -> Prop;
              equiv := fun l1 l2 => forall x, l1 x <-> l2 x; |}.
    abstract firstorder.
  Defined.

  Theorem lang_equiv : forall A (l1 l2: language A),
      (l1 == l2) =
      (forall x, l1 x <-> l2 x).
  Proof.
    reflexivity.
  Qed.

  Instance lang_Mo {A} : Monoid_Ops (language A) :=
    {| dot := fun (l1 l2: language A) =>
                fun s => exists s1 s2, s = s1 ++ s2 /\
                               l1 s1 /\
                               l2 s2;
       one := fun s => s = [] |}.

  Instance lang_SLo {A} : SemiLattice_Ops (language A) :=
    {| plus := fun (l1 l2: language A) => fun s => l1 s \/ l2 s;
       zero := fun s => False |}.

  Instance lang_Star {A} : Star_Op (language A) :=
    {| star := fun (l: language A) => star_l l |}.

  Lemma lang_equiv_destruct : forall A (l1 l2: language A),
      l1 == l2 ->
      (forall x, l1 x -> l2 x) /\
      (forall x, l2 x -> l1 x).
  Proof.
    intros.
    rewrite lang_equiv in H; firstorder.
  Qed.

  Ltac start :=
    repeat match goal with
           | |- forall _, _ => intros
           | |- _ <-> _ => split
           | |- _ == _ => rewrite lang_equiv
           | [ H: _ == _ |- _ ] => apply lang_equiv_destruct in H; destruct H
           | _ => setoid_rewrite <- app_assoc
           | _ => solve [ typeclasses eauto ]
           | _ => progress rewrite ?app_nil_l, ?app_nil_r
           | _ => progress unfold Proper, "==>", dot, plus
           | _ => progress simpl in *
           | _ => progress propositional
           end.

  Global Instance lang_Monoid : @Monoid (language A) lang_Mo.
  Proof.
    constructor; start; try solve [ intuition eauto 10 ].
    - eexists (_ ++ _), _;
        rewrite app_assoc;
        intuition eauto.
    - eexists _, _; intuition eauto.
      rewrite app_nil_l; auto.
    - eexists _, _; intuition eauto.
      rewrite app_nil_r; auto.
  Qed.

  Global Instance lang_SemiLattice : @SemiLattice (language A) lang_SLo.
  Proof.
    constructor; start; try solve [ intuition eauto 10 ].
  Qed.

  Global Instance lang_IdemSemiRing : @IdemSemiRing (language A) lang_Mo lang_SLo.
  Proof.
    constructor; start;
      try solve [ firstorder ].
  Qed.

  Hint Constructors star_l star_r.

  Global Instance lang_KleeneAlgebra : @KleeneAlgebra (language A) lang_Mo lang_SLo lang_Star.
  Proof.
    constructor; start; try solve [ intuition eauto 10 ].
    - (intuition eauto); propositional; eauto.
    - setoid_rewrite star_lr in H.
      rewrite star_lr.
      (intuition eauto); propositional; eauto.
    - (intuition eauto); propositional; eauto.
      induction H1; simpl.
      * apply H; auto.
      * rewrite <- app_assoc.
        apply H; eauto 10.
    - (intuition eauto); propositional; eauto.
      setoid_rewrite star_lr in H2.
      induction H2; rewrite ?app_nil_r.
      * apply H; eauto.
      * rewrite -> app_assoc.
        apply H; eauto 10.
  Qed.

End LanguageModel.

Section RelationalModel.
  Context {A:Type}.
  Definition relation : Setoid :=
    {| T := A -> A -> Prop;
       equiv r1 r2 := (forall x y, r1 x y -> r2 x y) /\ (forall x y, r2 x y -> r1 x y);
       equiv_Equiv := ltac:(firstorder) |}.

  Implicit Types r:relation.

  Instance rel_Mo : Monoid_Ops relation :=
    {| dot r1 r2 := fun x z => exists y, r1 x y /\ r2 y z;
       one := eq |}.

  Instance rel_SLo : SemiLattice_Ops relation :=
    {| plus r1 r2 := fun x y => r1 x y \/ r2 x y;
       zero := fun _ _ => False |}.

  Section RelationStar.

    Inductive kstar r : relation :=
    | kstar_refl : forall x, kstar r x x
    | kstar_one_more : forall x y z,
        r x y ->
        kstar r y z ->
        kstar r x z.

    Hint Constructors kstar.

    Inductive kstar_r r : relation :=
    | kstar_r_refl : forall x, kstar_r r x x
    | kstar_r_one_more : forall x y z,
        kstar_r r x y ->
        r y z ->
        kstar_r r x z.

    Hint Constructors kstar_r.

    Theorem kstar_lr: forall r x y,
        kstar r x y <-> kstar_r r x y.
    Proof.
      split; intros.
      - induction H; eauto.
        clear H0.
        induction IHkstar; eauto.
      - induction H; eauto.
        clear H.
        induction IHkstar_r; eauto.
    Qed.

  End RelationStar.

  Hint Constructors kstar kstar_r.

  Instance rel_Star : Star_Op relation :=
    {| star := kstar |}.

  Lemma rel_equiv : forall r1 r2,
      (r1 == r2) =
      ((forall x y, r1 x y -> r2 x y) /\ (forall x y, r2 x y -> r1 x y)).
  Proof.
    intros.
    reflexivity.
  Qed.

  Ltac start :=
    repeat match goal with
           | |- forall _, _ => intros
           | |- _ /\ _ => split
           | |- _ == _ => rewrite rel_equiv
           | [ H: _ == _ |- _ ] => rewrite rel_equiv in H; destruct H
           | _ => setoid_rewrite <- app_assoc
           | _ => solve [ typeclasses eauto ]
           | _ => progress rewrite ?app_nil_l, ?app_nil_r
           | _ => progress unfold Proper, "==>", dot, plus
           | _ => progress simpl in *
           | _ => progress propositional
           end.

  Global Instance rel_Monoid : @Monoid relation rel_Mo.
  Proof.
    constructor; start; eauto.
  Qed.

  Global Instance rel_SemiLattice : @SemiLattice relation rel_SLo.
  Proof.
    constructor; start; intuition eauto.
  Qed.

  Global Instance rel_IdemSemiRing : @IdemSemiRing relation rel_Mo rel_SLo.
  Proof.
    constructor; start; intuition (propositional; eauto).
  Qed.

  Global Instance rel_KA : @KleeneAlgebra relation rel_Mo rel_SLo rel_Star.
  Proof.
    constructor; start; intuition (propositional; eauto).
    - rewrite kstar_lr in *; eauto.
    - induction H0; eauto 10.
    - rewrite kstar_lr in *.
      induction H2; eauto 10.
  Qed.

End RelationalModel.
