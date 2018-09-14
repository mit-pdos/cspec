Require Import Morphisms.
Require Import Setoid.
Require PeanoNat.
Require List.

Require Import Helpers.ProofAutomation.Propositional.

Set Implicit Arguments.

Module Type KleeneAlgebra.
  Axiom K:Type.
  Axiom equiv: K -> K -> Prop.
  Axiom equiv_Equivalence : Equivalence equiv.
  Existing Instance equiv_Equivalence.

  Axiom choice : K -> K -> K.
  Axiom seq : K -> K -> K.
  Axiom star : K -> K.

  Axiom choice_respects_equiv : Proper (equiv ==> equiv ==> equiv) choice.
  Existing Instance choice_respects_equiv.
  Axiom seq_respects_equiv : Proper (equiv ==> equiv ==> equiv) seq.
  Existing Instance seq_respects_equiv.
  Axiom star_respects_equiv : Proper (equiv ==> equiv) star.
  Existing Instance star_respects_equiv.

  Axiom fail : K.
  Axiom skip : K.

  Definition le (a b:K) := equiv (choice a b) b.

  Module KANotations.
    Infix "==" := equiv (at level 90).
    Infix "+" := choice.
    Infix "*" := seq.
    Notation "R ^*" := (star R) (at level 0, format "'[' R ']' ^*").
    Notation "0" := fail.
    Notation "1" := skip.
    Infix "<=" := le.
  End KANotations.

  Import KANotations.

  (** Idempotent semiring *)
  Section Axioms.
    Context (p q r:K).
    Axiom choice_assoc : p + (q + r) == (p + q) + r.
    Axiom seq_assoc : p * (q * r) == (p * q) * r.
    Axiom choice_comm : p + q == q + p.
    Axiom distr_l : p * (q + r) == p * q + p * r.
    Axiom distr_r : (p + q) * r == p * r + q * r.
    Axiom choice_id_r : p + 0 == p.
    Axiom choice_idem : p + p == p.
    Axiom fail_cancel_r : p * 0 == 0.
    Axiom fail_cancel_l : 0 * p == 0.
    Axiom skip_id_l : 1 * p == p.
    Axiom skip_id_r : p * 1 == p.
  End Axioms.

  (** Axioms for star *)
  Section StarAxioms.
    Context (p q x:K).
    Axiom star_one_l : 1 + p * p^* <= p^*.
    Axiom star_one_r : 1 + p^* * p <= p^*.
    Axiom star_ind_l : q + p * x <= x -> p^* * q <= x.
    Axiom star_ind_r : q + x * p <= x -> q * p^* <= x.
  End StarAxioms.

End KleeneAlgebra.

Module KAFacts (Import A:KleeneAlgebra).
  Import A.KANotations.

  Existing Instance equiv_Equivalence.

  Theorem le_eq : forall p q, p <= q ->
                          q <= p ->
                          p == q.
  Proof.
    unfold le; intros.
    rewrite <- H.
    rewrite <- H0 at 1.
    apply choice_comm.
  Qed.

  Hint Rewrite choice_idem : ka.
  Hint Rewrite choice_assoc : ka.
  Hint Rewrite seq_assoc : ka.
  Hint Rewrite choice_id_r : ka.

  Lemma choice_id_l : forall x, 0 + x == x.
  Proof.
    intros.
    rewrite choice_comm.
    apply choice_id_r.
  Qed.

  Hint Rewrite choice_id_l : ka.

  Hint Rewrite fail_cancel_r fail_cancel_r skip_id_l skip_id_r : ka.

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

  Hint Rewrite distr_r distr_l : ka_distr.

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

  Hint Resolve choice_idem le_eq.
  Hint Resolve (reflexivity : forall x, x == x).

  Instance le_PreOrder : PreOrder le.
  Proof.
    constructor; repeat (hnf; intros); auto.
    unfold le in *.
    rewrite <- H0.
    rewrite <- H at 2.
    cleanup.
  Qed.

  Instance le_PartialOrder : PartialOrder equiv le.
  Proof.
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
    rewrite <- choice_assoc.
    rewrite (choice_comm b c).
    cleanup.
  Qed.

  Instance le_choice_respectful :
    Proper (le ==> le ==> le) choice.
  Proof.
    autounfold with m; unfold le; intros.
    cleanup.
    rewrite (abc_to_acb x x0 y).
    rewrite H.
    rewrite <- choice_assoc.
    rewrite H0.
    auto.
  Qed.

  Instance le_star_sub : subrelation equiv le.
  Proof.
    hnf; intros.
    unfold le; cleanup.
  Qed.

  Lemma distr_abcd : forall a b c d,
      (a + b) * (c + d) ==
      a * c + b * d + (a * d + b * c).
  Proof.
    intros.
    rewrite ?distr_l, ?distr_r.
    generalize dependent (a*c); intro w.
    generalize dependent (b*c); intro x.
    generalize dependent (a*d); intro y.
    generalize dependent (b*d); intro z.
    rewrite (choice_comm y z).
    rewrite choice_assoc at 1.
    rewrite (abc_to_acb w x z).
    rewrite (choice_comm y x).
    cleanup.
  Qed.

  Instance le_seq_respectful :
      Proper (le ==> le ==> le) seq.
  Proof.
    autounfold with m; intros.
    unfold le in *.

    assert ((x + y) * (x0 + y0) == y * y0).
    rewrite H, H0; auto.
    rewrite <- H1 at 2.

    rewrite distr_abcd.
    rewrite <- (choice_idem (x * x0 + y * y0)) at 2.
    rewrite <- choice_assoc.

    assert (x * x0 + y * y0 + (x * y0 + y * x0) ==
            (x + y) * (x0 + y0)).
    rewrite abc_to_acb.
    rewrite ?distr_l, ?distr_r; cleanup.
    rewrite (abc_to_acb (x*x0) (x*y0) (y*x0)).
    auto.

    rewrite H2.
    rewrite H1.
    rewrite <- choice_assoc.
    rewrite choice_idem.
    auto.
  Qed.

  Theorem choice_r_monotone : forall r p q,
      p <= q ->
      p + r <= q + r.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Theorem choice_l_monotone : forall r p q,
      p <= q ->
      r + p <= r + q.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Theorem seq_r_monotone : forall r p q,
      p <= q ->
      p * r <= q * r.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Theorem seq_l_monotone : forall r p q,
      p <= q ->
      r * p <= r * q.
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

  Theorem star_ind1_l : forall p x, 1 + p * x <= x -> p^* <= x.
  Proof.
    intros.
    eapply star_ind_l in H.
    cleanup; auto.
  Qed.

  Theorem star_ind1_r : forall p x, 1 + x * p <= x -> p^* <= x.
  Proof.
    intros.
    eapply star_ind_r in H.
    cleanup.
  Qed.

  Theorem star_and : forall p q,
      q + p*p^* * q <= p^* * q.
  Proof.
    intros.
    pose proof (star_one_l p).
    apply (seq_r_monotone q) in H.
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

  Theorem choice_le_r : forall p q,
      p <= p + q.
  Proof.
    intros.
    unfold le; cleanup.
  Qed.

  Theorem choice_le_l : forall p q,
      p <= q + p.
  Proof.
    intros.
    rewrite choice_comm.
    apply choice_le_r.
  Qed.

  Hint Resolve (reflexivity : forall p, p <= p).

  Ltac monotonicity :=
    match goal with
    | [ |- ?x * _ <= ?x * _ ] =>
      apply seq_l_monotone
    | [ |- _ * ?y <= _ * ?y ] =>
      apply seq_r_monotone
    | [ |- ?x + _ <= ?x + _ ] =>
      apply choice_l_monotone
    | [ |- _ + ?y <= _ + ?y ] =>
      apply choice_r_monotone
    | [ |- ?x + _ == ?x + _ ] =>
      apply choice_respects_equiv; [ reflexivity | ]
    | [ |- _ + ?y == _ + ?y ] =>
      apply choice_respects_equiv; [ | reflexivity ]
    | [ |- ?p <= ?p + _ ] =>
      apply choice_le_r
    | [ |- ?p <= _ + ?p ] =>
      apply choice_le_l
    end.

  Lemma choice_split : forall p q x,
      p <= x ->
      q <= x ->
      p + q <= x.
  Proof.
    unfold le; intros.
    rewrite <- choice_assoc.
    rewrite H0.
    auto.
  Qed.

  Theorem star_expand p :
      p^* == 1 + p * p^*.
  Proof.
    apply le_eq; [ | apply star_one_l ].
    apply star_ind1_l; cleanup.
    repeat monotonicity.
    apply star_one_l.
  Qed.

  Theorem star_expand_l p :
      p^* == 1 + p^* * p.
  Proof.
    apply le_eq; [ | apply star_one_r ].
    apply star_ind1_r; cleanup.
    repeat monotonicity.
    apply star_one_r.
  Qed.

  Lemma star_one_l p :
      p * p^* <= p^*.
  Proof.
    unfold le; intros.
    rewrite star_expand at 2 3.
    cleanup.
    rewrite abc_to_acb.
    cleanup.
    rewrite choice_comm; auto.
  Qed.

  Theorem star_incl_skip p :
    1 <= p^*.
  Proof.
    intros.
    rewrite star_expand.
    monotonicity.
  Qed.

  Theorem star_expand1 p : p^* == 1 + p^*.
  Proof.
    apply le_eq.
    - rewrite star_expand at 1.
      monotonicity.
      apply star_one_l.
    - rewrite (star_incl_skip p); cleanup.
  Qed.

  Lemma star_one_r p :
      p^* * p <= p^*.
  Proof.
    unfold le; intros.
    rewrite star_expand_l at 2 3.
    cleanup.
    rewrite abc_to_acb.
    cleanup.
    rewrite choice_comm; auto.
  Qed.

  Hint Resolve star_one_l star_one_r.

  Theorem star_one_comm p : p * p^* == p^* * p.
  Proof.
    apply le_eq.
    - apply star_ind_r.
      rewrite star_one_r at 1.
      rewrite star_expand1 at 2; cleanup_distr.
    - apply star_ind_l.
      rewrite star_one_l at 1.
      rewrite star_expand1 at 2; cleanup_distr.
  Qed.

  Theorem star_square p : p^* == p^* * p^*.
  Proof.
    apply le_eq.
    - rewrite <- skip_id_r at 1.
      monotonicity.
      apply star_incl_skip.
    - apply star_ind_l.
      apply choice_split; auto.
  Qed.

  Theorem star_repeat p : p^*^* == p^*.
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
      w * x * y * z == w * (x * y) * z.
  Proof.
    cleanup.
  Qed.

  Theorem sliding p q : (p * q)^* * p == p * (q * p)^*.
  Proof.
    apply le_eq.
    - apply star_ind_l; cleanup.
      rewrite quad_product_middle.
      generalize dependent (q * p); intro y.
      rewrite (star_expand y) at 2; cleanup_distr.
    - apply star_ind_r; cleanup.
      rewrite quad_product_middle.
      generalize dependent (p * q); intro y.
      rewrite (star_expand_l y) at 2; cleanup_distr.
  Qed.

  Theorem seq_le_star p q r :
    p <= r^* ->
    q <= r^* ->
    p * q <= r^*.
  Proof.
    intros.
    rewrite H.
    rewrite H0.
    rewrite <- star_square; auto.
  Qed.

  Lemma star_one_iter : forall p,
      p <= p^*.
  Proof.
    intros.
    rewrite star_expand.
    rewrite <- star_incl_skip; cleanup.
    monotonicity.
  Qed.

  Theorem star_one_le : forall p q,
      p <= q ->
      p <= q^*.
  Proof.
    intros.
    rewrite <- star_one_iter; auto.
  Qed.

  Hint Resolve star_one_le.
  Hint Resolve choice_le_l choice_le_r.

  Theorem denesting p q : (p + q)^* == p^* * (q * p^*)^*.
  Proof.
    apply le_eq.
    - apply star_ind1_l; cleanup.
      apply choice_split.
      + repeat rewrite <- star_incl_skip at 1; cleanup.
      + cleanup_distr.
        apply choice_split.
        monotonicity; auto.
        rewrite (star_square (q * _)) at 2; cleanup.
        monotonicity.
        rewrite <- star_incl_skip at 2; cleanup.
        auto.
    - apply star_ind_l.
      apply choice_split.
      + apply star_ind1_l.
        rewrite (star_expand1 (p+q)) at 2.
        monotonicity.
        repeat apply seq_le_star; auto.
        apply le_star_respectful; auto.
      + rewrite (choice_le_r p q) at 1.
        apply star_one_l.
  Qed.

  Theorem bisimulation p q r :
    p * q == q * r ->
    p^* * q == q * r^*.
  Proof.
    intros.
    apply le_eq.
    - apply star_ind_l; cleanup.
      rewrite H.
      rewrite (star_expand r) at 2; cleanup_distr.
    - apply star_ind_r; cleanup.
      rewrite <- seq_assoc.
      rewrite <- H; cleanup.
      rewrite (star_expand_l p) at 2; cleanup_distr.
  Qed.
End KAFacts.

Module Type Alphabet.
  Axiom A:Type.
End Alphabet.

Module LanguageModel (Import A:Alphabet) <: KleeneAlgebra.
  (* the elements of the language model are regular languages *)
  Definition K := list A -> Prop.
  Definition equiv : K -> K -> Prop := fun l1 l2 => forall x, l1 x <-> l2 x.

  Import List List.ListNotations.
  Open Scope list.

  Notation magic := ltac:(firstorder) (only parsing).

  Instance equiv_Equivalence : Equivalence equiv := magic.

  Definition choice : K -> K -> K :=
    fun l1 l2 s => l1 s \/ l2 s.
  Definition seq : K -> K -> K :=
    fun l1 l2 s => exists s1 s2, s = s1 ++ s2 /\
                         l1 s1 /\
                         l2 s2.
  Inductive star_l (l: list A -> Prop) : list A -> Prop :=
  | star_empty : star_l l []
  | star_one_more : forall s s',
      l s ->
      star_l l s' ->
      star_l l (s ++ s').

  Hint Constructors star_l.

  Definition star : K -> K := star_l.

  Instance choice_respects_equiv : Proper (equiv ==> equiv ==> equiv) choice
    := magic.
  Instance seq_respects_equiv : Proper (equiv ==> equiv ==> equiv) seq
    := magic.

  Instance star_respects_equiv : Proper (equiv ==> equiv) star.
  Proof.
    unfold equiv, star.
    repeat (hnf; intros); intuition auto.
    induction H0; eauto; firstorder.
    induction H0; eauto; firstorder.
  Qed.

  Definition fail : K := fun _ => False.
  Definition skip : K := fun s => s = nil.

  Definition le (a b:K) := equiv (choice a b) b.

  Module KANotations.
    Infix "==" := equiv (at level 90).
    Infix "+" := choice.
    Infix "*" := seq.
    Notation "R ^*" := (star R) (at level 0, format "'[' R ']' ^*").
    Notation "0" := fail.
    Notation "1" := skip.
    Infix "<=" := le.
  End KANotations.

  Import KANotations.

  (** Idempotent semiring *)
  Section Axioms.
    Context (p q r:K).
    Definition choice_assoc : p + (q + r) == (p + q) + r := magic.
    Theorem seq_assoc : p * (q * r) == (p * q) * r.
      unfold seq, equiv; intros.
      split; propositional.
      eexists (_ ++ _), _; rewrite <- app_assoc; intuition eauto.
      eexists _, (_ ++ _); rewrite <- app_assoc; intuition eauto.
    Qed.

    Definition choice_comm : p + q == q + p := magic.
    Definition distr_l : p * (q + r) == p * q + p * r := magic.
    Definition distr_r : (p + q) * r == p * r + q * r := magic.
    Definition choice_id_r : p + 0 == p := magic.
    Definition choice_idem : p + p == p := magic.
    Definition fail_cancel_r : p * 0 == 0 := magic.
    Definition fail_cancel_l : 0 * p == 0 := magic.
    Theorem skip_id_l : 1 * p == p.
      unfold seq, equiv, "1"; split; propositional.
      do 2 eexists; intuition eauto.
      simpl; auto.
    Qed.
    Theorem skip_id_r : p * 1 == p.
      unfold seq, equiv, "1"; split; propositional.
      rewrite app_nil_r; auto.
      do 2 eexists; intuition eauto.
      rewrite app_nil_r; auto.
    Qed.
  End Axioms.

  Definition le_implies : forall (x y:K),
      (forall s, x s -> y s) ->
      x <= y := magic.

  Definition le_implies' : forall (x y:K),
      x <= y ->
      (forall s, x s -> y s) := magic.

  Ltac le := intros;
             repeat match goal with
                      | |- _ <= _ => apply le_implies
                      | [ H: _ <= _ |- _ ] => pose proof (le_implies' H);
                                           clear H
                    end;
             unfold choice, seq, "1", star in *;
             intros.

  Lemma star_l_one : forall (x:K) s,
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

  Theorem star_r_one : forall (x:K) s,
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

  (** Axioms for star *)
  Section StarAxioms.
    Context (p q x:K).
    Theorem star_one_l : 1 + p * p^* <= p^*.
    Proof.
      le.
      (intuition propositional); eauto.
    Qed.

    Theorem star_one_r : 1 + p^* * p <= p^*.
    Proof.
      le.
      setoid_rewrite star_lr in H.
      setoid_rewrite star_lr.
      (intuition propositional); eauto.
    Qed.

    Theorem star_ind_l : q + p * x <= x -> p^* * q <= x.
    Proof.
      le.
      (intuition propositional); eauto.
      induction H1; eauto.
      rewrite <- app_assoc; eauto 10.
    Qed.

    Theorem star_ind_r : q + x * p <= x -> q * p^* <= x.
    Proof.
      le.
      setoid_rewrite star_lr in H.
      (intuition propositional); eauto.
      induction H2; rewrite ?app_nil_r; eauto.
      rewrite app_assoc.
      eauto 10.
    Qed.
  End StarAxioms.
End LanguageModel.
