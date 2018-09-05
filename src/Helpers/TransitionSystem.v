Require Import Helpers.Instances.
Require Import Helpers.ProofAutomation.

Require Import Morphisms.

Set Implicit Arguments.

Generalizable Variable R.

Section TransitionSystem.
  Variable A:Type.

  Definition Relation := A -> A -> Prop.
  Implicit Types (R:Relation).

  Definition rimpl R1 R2 := forall x y, R1 x y -> R2 x y.
  Definition riff R1 R2 := rimpl R1 R2 /\ rimpl R2 R1.

  Infix "--->" := rimpl (at level 40, no associativity).
  Infix "<--->" := riff (at level 40, no associativity).

  Notation magic := (ltac:(firstorder)) (only parsing).

  Global Instance rimpl_PreOrder : PreOrder rimpl := magic.
  Global Instance riff_Equivalence : Equivalence riff := magic.

  Global Instance riff_rimpl : subrelation riff rimpl := magic.

  Inductive kleene_star R : Relation :=
  | star_refl : forall x,
      kleene_star R x x
  | star_one : forall x1 x2 x3,
      R x1 x2 ->
      kleene_star R x2 x3 ->
      kleene_star R x1 x3.

  Global Instance kleene_star_PreOrder : PreOrder (kleene_star R).
  Proof.
    RelInstance_t.
    - constructor.
    - induction H; eauto using kleene_star.
  Qed.

  Theorem kleene_star_one : forall R, R ---> kleene_star R.
  Proof.
    unfold rimpl.
    eauto using kleene_star.
  Qed.

  Global Instance kleene_star_sub : subrelation R (kleene_star R) :=
    kleene_star_one.

  Global Instance kleene_star_respects_sub :
    Proper (rimpl ==> rimpl) kleene_star.
  Proof.
    unfold Proper, rimpl, "==>"; intros.
    induction H0; eauto using kleene_star.
  Qed.

  Global Instance kleene_star_respects_sub_expanded :
    Proper (rimpl ==> eq ==> eq ==> Basics.impl) kleene_star.
  Proof.
    unfold Proper, rimpl, Basics.impl, "==>"; propositional.
    eapply kleene_star_respects_sub; eauto.
  Qed.

  Definition invariant (I: A -> Prop) R :=
    forall x1, I x1 ->
          forall x2, R x1 x2 -> I x2.

  Theorem invariant_star : forall I R,
      invariant I R ->
      invariant I (kleene_star R).
  Proof.
    unfold invariant; intros.
    induction H1; eauto.
  Qed.

  Theorem invariant_star' : forall I R,
      invariant I (kleene_star R) ->
      invariant I R.
  Proof.
    unfold invariant; intros.
    eapply H; eauto.
    eapply kleene_star_one; eauto.
  Qed.

  Global Instance invariant_impl I :
    Proper (riff ==> Basics.impl) (invariant I) := magic.

  Definition rel_app R1 R2 : Relation :=
    fun x z => exists y, R1 x y /\ R2 y z.

  Infix ">>" := rel_app (at level 12, left associativity).

  Definition rel_app_assoc R1 R2 R3 :
    R1 >> (R2 >> R3) <---> R1 >> R2 >> R3 := magic.

  Hint Rewrite rel_app_assoc : rel.

  Global Instance rel_app_impl :
    Proper (rimpl ==> rimpl ==> rimpl) rel_app := magic.

  Global Instance rel_app_iff :
    Proper (riff ==> riff ==> riff) rel_app := magic.

  Theorem po_dup R {tr:PreOrder R} : R <---> R >> R.
  Proof.
    split; unfold rimpl; propositional.
    - exists x; split; [ reflexivity | ]; auto.
    - destruct H; propositional.
      transitivity x0; auto.
  Qed.

  Theorem kleene_star_dup : forall R,
      kleene_star R <---> kleene_star R >> kleene_star R.
  Proof.
    intros.
    apply po_dup.
  Qed.

  Definition rel_plus R1 R2 : Relation :=
    fun x y => R1 x y \/ R2 x y.

  Infix "+++" := (rel_plus) (at level 13, left associativity).

  Global Instance rel_plus_impl :
    Proper (rimpl ==> rimpl ==> rimpl) rel_plus := magic.
  Global Instance rel_plus_iff :
    Proper (riff ==> riff ==> riff) rel_plus := magic.

  Definition rel_app_distr_r R1 R2 R3 :
      (R1 +++ R2) >> R3 <---> R1 >> R3 +++ R2 >> R3 := magic.

  Definition rel_app_distr_l R1 R2 R3 :
      R1 >> (R2 +++ R3) <---> R1 >> R2 +++ R1 >> R3 := magic.

  Hint Rewrite rel_app_distr_r rel_app_distr_l : rel.

  Definition rel_plus_assoc R1 R2 R3 :
      R1 +++ (R2 +++ R3) <---> R1 +++ R2 +++ R3 := magic.

  Hint Rewrite rel_plus_assoc : rel.

  Definition rel_next R1 R2 : Relation :=
    R1 +++ R1 >> R2.

  Infix "?>" := (rel_next) (at level 11, right associativity).

  Global Instance rel_next_impl :
    Proper (rimpl ==> rimpl ==> rimpl) rel_next := magic.
  Global Instance rel_next_iff :
    Proper (riff ==> riff ==> riff) rel_next := magic.

  Global Instance proper_rimpl :
      Proper (rimpl ==> riff ==> Basics.flip Basics.impl) rimpl := magic.

  Definition rel_next_associative R1 R2 R3 :
      R1 ?> R2 ?> R3 ---> (R1 ?> R2) ?> R3 := magic.

  Definition noop : Relation := eq.

  Theorem star_expand_or : forall R,
      kleene_star R <---> noop +++ R >> kleene_star R.
  Proof.
    unfold noop.
    split; repeat (hnf; intros).
    - destruct H; firstorder.
    - firstorder; subst; eauto using kleene_star.
  Qed.

  Global Instance riff_proper :
    Proper (riff ==> riff ==> Basics.flip Basics.impl) riff := magic.

  Theorem star_expand_next : forall R,
      kleene_star R <---> noop ?> R ?> kleene_star R.
  Proof.
    intros.
    unfold noop.
    split; repeat (hnf; intros).
    - destruct H; firstorder.
    - firstorder; subst; eauto using kleene_star.
  Qed.

  Definition seq_star_eps : forall R1 R2,
      R1 --->
      R1 >> kleene_star R2 := magic.

  Lemma star_intro1 R :
    noop ---> kleene_star R.
  Proof.
    unfold ">>", "--->", noop; propositional.
    eauto using kleene_star.
  Qed.

  Lemma star_intro2 R :
    R >> kleene_star R ---> kleene_star R.
  Proof.
    unfold ">>", "--->"; propositional.
    eauto using kleene_star.
  Qed.

  Theorem noop_seq_l R :
    noop >> R <---> R.
  Proof.
    split; unfold ">>", "--->", noop; propositional.
    eexists; intuition eauto.
  Qed.

  Theorem noop_seq_r R :
    R >> noop <---> R.
  Proof.
    split; unfold ">>", "--->", noop; propositional.
    eexists; intuition eauto.
  Qed.

  Definition rel_plus_distr_app R1 R2 R3 :
    (R1 >> R3) +++ (R2 >> R3) <--->
               (R1 +++ R2) >> R3 := magic.

  Definition rel_plus_distr_next R1 R2 R3 :
    (R1 ?> R3) +++ (R2 ?> R3) <--->
               (R1 +++ R2) ?> R3 := magic.

  Definition rel_plus_elim R1 R2 R3 :
    R1 ---> R3 ->
    R2 ---> R3 ->
    R1 +++ R2 ---> R3 := magic.

  Definition next_cancel_r R1 R2 R2' :
    R2 ---> R2' ->
    R2 ?> R1 ---> R2' ?> R1 := magic.

  Definition next_cancel_l R1 R2 R2' :
    R2 ---> R2' ->
    R1 ?> R2 ---> R1 ?> R2' := magic.

  Definition app_cancel_r R1 R2 R2' :
    R2 ---> R2' ->
    R2 >> R1 ---> R2' >> R1 := magic.

  Definition app_cancel_l R1 R2 R2' :
    R2 ---> R2' ->
    R1 >> R2 ---> R1 >> R2' := magic.

  Lemma next_star_prepend : forall R1 R2,
      R1 >> kleene_star R1 ?> R2 --->
         kleene_star R1 ?> R2.
  Proof.
    unfold ">>", "--->"; propositional.
    destruct H0.
    left; eauto using kleene_star.
    right.
    destruct H0; propositional.
    exists x0; intuition eauto using kleene_star.
  Qed.

  Lemma app_star_prepend : forall R1 R2,
      R1 >> kleene_star R1 >> R2 --->
         kleene_star R1 >> R2.
  Proof.
    unfold ">>", "--->"; propositional.
    exists y0; intuition eauto using kleene_star.
  Qed.

  Definition next_kleene_star R1 R2 :
      R1 ?> kleene_star R2 <---> R1 >> kleene_star R2 := magic.

  Definition trans_dup R {tr:Transitive R} : R <---> R ?> R := magic.

  Theorem kleene_star_dup_next R :
      kleene_star R <---> kleene_star R ?> kleene_star R.
  Proof.
    apply trans_dup.
  Qed.

  Theorem star_ind R1 R2 :
    noop ---> R2 ->
    R1 >> R2 ---> R2 ->
    kleene_star R1 ---> R2.
  Proof.
    unfold "--->", ">>", noop; intros.
    induction H1; eauto.
  Qed.

  Definition app_next_assoc R1 R2 R3 :
    R1 >> R2 ?> R3 <--->
       (R1 >> R2) ?> R3 := magic.

  Definition next_intro1 R1 R2 : R1 ---> R1 ?> R2 := magic.
  Definition next_intro2 R1 R2 : R1 >> R2 ---> R1 ?> R2 := magic.

  Definition rel_apply R (f1 f2: A -> A) : Relation :=
    fun x y => R (f1 x) (f2 y).

  Theorem rel_apply_star_commute : forall R f,
      kleene_star (rel_apply R f f) --->  rel_apply (kleene_star R) f f.
  Proof.
    unfold "--->", rel_apply; intros.
    induction H; eauto using kleene_star.
  Qed.

End TransitionSystem.

Arguments noop {A}.

Infix "--->" := rimpl (at level 40, no associativity) : relation_scope.
Infix "<--->" := riff (at level 40, no associativity) : relation_scope.
Infix "+++" := (rel_plus) (at level 18, left associativity).
Infix ">>" := rel_app (at level 11, right associativity) : relation_scope.
Infix "?>" := (rel_next) (at level 11, right associativity) : relation_scope.
Delimit Scope relation_scope with rel.
