Require Import RelationClasses.
Require Import Setoid.
Require Import Morphisms.
Require PeanoNat.
Require List.

Unset Intuition Negation Unfolding.
Set Implicit Arguments.

Module Type BooleanAlgebra.
  Parameter B:Type.
  Parameter equiv: B -> B -> Prop.
  Parameter equiv_Equiv : Equivalence equiv.
  Existing Instance equiv_Equiv.

  Infix "==" := equiv (at level 90).

  Parameter or: B -> B -> B.
  Parameter and : B -> B -> B.
  Parameter not: B -> B.

  Axiom or_respects_equiv : Proper (equiv ==> equiv ==> equiv) or.
  Axiom and_respects_equiv : Proper (equiv ==> equiv ==> equiv) and.
  Axiom not_respects_equiv : Proper (equiv ==> equiv) not.

  Existing Instances or_respects_equiv and_respects_equiv not_respects_equiv.

  Parameter zero : B.
  Parameter one : B.

  Module BANotations.
    Infix "+" := or.
    Infix "*" := and.
    Notation "! x" := (not x) (at level 10, format "! x").
    Notation "0" := zero.
    Notation "1" := one.
  End BANotations.
  Import BANotations.

  Section Laws.
    Context (a b c:B).
    Axiom or_assoc : a + (b + c) == a + b + c.
    Axiom or_comm : a + b == b + a.
    Axiom or_zero : a + 0 == a.
    Axiom or_one : a + 1 == 1.
    Axiom or_absorption : a + a == a.
    Axiom and_or_distr : a*(b + c) == a*b + a*c.
    Axiom not_or_distr : !(a + b) == !a * !b.

    Axiom zero_dual : !0 == 1.
    Axiom one_dual : !1 == 0.
    Axiom double_neg : !(!a) == a.
  End Laws.
End BooleanAlgebra.

Module BAFacts (Import A:BooleanAlgebra).
  Import A.BANotations.

  Class Default A := default_val: A.

  Module varmap.
    Definition I := nat.
    Inductive t (A:Type) : Type :=
    | empty
    | cons (i:I) (x:A) (xs:t A).

    Definition index_eq (i1 i2:I) : bool :=
      Nat.eqb i1 i2.

    Theorem index_eq_prop : forall i1 i2,
        index_eq i1 i2 = true <-> i1 = i2.
    Proof.
      apply PeanoNat.Nat.eqb_eq.
    Qed.

    Fixpoint find {A} `{Default A} (i:nat) (vm: t A) : A :=
      match vm with
      | empty _ => default_val
      | cons i' x vm' => if Nat.eqb i i' then x else find i vm'
      end.

    Fixpoint length A (ctx: t A) : nat :=
      match ctx with
      | empty _ => O
      | cons _ _ ctx' => S (length ctx')
      end.

  End varmap.

  Instance B_def : Default B := 0.

  Section Ops.

    Inductive op_tree :=
    | Leaf (x:B)
    | Atom (i:varmap.I)
    | Const0
    | Const1
    | NegNode (t: op_tree)
    | OrNode (l r: op_tree)
    | AndNode (l r: op_tree).

    Fixpoint interpret (vm: varmap.t B) t :=
      match t with
      | Leaf x => x
      | Atom i => varmap.find i vm
      | Const0 => 0
      | Const1 => 1
      | NegNode t => not (interpret vm t)
      | OrNode l r => or (interpret vm l) (interpret vm r)
      | AndNode l r => and (interpret vm l) (interpret vm r)
      end.

  End Ops.

  Fixpoint dual_t (t:op_tree) : op_tree :=
    match t with
    | Leaf x => Leaf (!x)
    | Atom i => NegNode (Atom i)
    | Const0 => Const1
    | Const1 => Const0
    | NegNode x => NegNode (dual_t x)
    | OrNode l r => AndNode (dual_t l) (dual_t r)
    | AndNode l r => OrNode (dual_t l) (dual_t r)
    end.

  Hint Resolve (reflexivity : forall x, x == x).

  Theorem dual_eq : forall a b,
      !a == !b ->
      a == b.
  Proof.
    intros.
    apply not_respects_equiv in H.
    rewrite ?double_neg in *; auto.
  Qed.

  Theorem not_and_distr : forall a b, !(a * b) == !a + !b.
  Proof.
    intros.
    apply dual_eq.
    rewrite not_or_distr; auto.
    rewrite ?double_neg; auto.
  Qed.

  Ltac simp :=
    autorewrite with b in *;
    trivial.

  Hint Rewrite or_assoc or_zero or_absorption : b.
  Hint Rewrite double_neg : b.
  Hint Rewrite zero_dual one_dual : b.

  Theorem dual_t_negation : forall vm t,
      !(interpret vm t) == interpret vm (dual_t t).
  Proof.
    symmetry.
    induction t; simpl; simp.
    - rewrite IHt; simp.
    - rewrite IHt1, IHt2; simp.
      rewrite not_or_distr; simp.
    - rewrite IHt1, IHt2; simp.
      rewrite not_and_distr; simp.
  Qed.

  Ltac reify_helper term ctx :=
    let reify_rec term ctx := reify_helper term ctx in
    lazymatch ctx with
    | context[varmap.cons ?i term _] =>
      constr:( (ctx, Atom i) )
    | _ =>
      lazymatch term with
      | 0 => constr:( (ctx, Const0) )
      | 1 => constr:( (ctx, Const1) )
      | not ?x =>
        let ctx_x := reify_rec x ctx in
        let r := (eval cbv [fst snd] in
                     (fst ctx_x, NegNode (snd ctx_x))) in
        constr:(r)
      | or ?x ?y =>
        let ctx_x := reify_rec x ctx in
        let ctx_y := reify_rec y (fst ctx_x) in
        let r := (eval cbv [fst snd] in
                     (fst ctx_y, OrNode (snd ctx_x) (snd ctx_y))) in
        constr:(r)
      | and ?x ?y =>
        let ctx_x := reify_rec x ctx in
        let ctx_y := reify_rec y (fst ctx_x) in
        let r := (eval cbv [fst snd] in
                     (fst ctx_y, AndNode (snd ctx_x) (snd ctx_y))) in
        constr:(r)
      | _ =>
        let v' := (eval cbv [varmap.length] in (varmap.length ctx)) in
        let ctx' := constr:( varmap.cons v' term ctx ) in
        constr:( (ctx', Atom v') )
      end
    end.

  Ltac reify term :=
    reify_helper term (varmap.empty B).

  Ltac quote_with ctx term :=
    let ctx_x := reify_helper term ctx in
    let ctx := (eval cbv [fst] in (fst ctx_x)) in
    let x := (eval cbv [snd] in (snd ctx_x)) in
    change term with (interpret ctx x).
  Ltac quote term := quote_with (varmap.empty B) term.

  Ltac quote_eqn :=
    match goal with
    | |- ?x == _ =>
      quote x;
      match goal with
      | |- interpret ?ctx _ == ?y =>
        quote_with ctx y
      end
    end.

  Theorem dual_interpret_eq : forall vm vm' t1 t2,
      interpret vm (dual_t t1) == interpret vm' (dual_t t2) ->
      interpret vm t1 == interpret vm' t2.
  Proof.
    intros.
    apply dual_eq.
    rewrite ?dual_t_negation; auto.
  Qed.

  Ltac dualize :=
    intros;
    quote_eqn;
    apply dual_interpret_eq;
    simpl.

  Theorem and_one : forall a, a * 1 == a.
  Proof.
    dualize.
    apply or_zero.
  Qed.

  Theorem and_zero : forall a, a * 0 == 0.
  Proof.
    dualize.
    apply or_one.
  Qed.

  Theorem zero_or : forall a, 0 + a == a.
  Proof.
    intros.
    rewrite or_comm, or_zero; auto.
  Qed.

  Theorem and_or : forall a, a * 0 == 0.
  Proof.
    dualize.
    apply or_one.
  Qed.

  Theorem one_and : forall a, 1 * a == a.
  Proof.
    dualize.
    apply zero_or.
  Qed.

  Theorem unique_zero : forall o,
      (forall x, x + o == x) -> o == 0.
  Proof.
    intros.
    specialize (H 0).
    rewrite zero_or in H; auto.
  Qed.

  Theorem unique_one : forall o,
      (forall x, x * o == x) -> o == 1.
  Proof.
    intros.
    specialize (H 1).
    rewrite one_and in H; auto.
  Qed.

End BAFacts.

Module DecidableProp : BooleanAlgebra.
  Record DecProp := { P :> Prop;
                      dec: {P} + {~P} }.
  Definition B := DecProp.

  Theorem dec_dn : forall (p:DecProp),
      (~p -> False) ->
      p.
  Proof.
    intros.
    destruct (dec p); tauto.
  Qed.

  Hint Resolve dec_dn.

  Definition equiv (p1 p2: B) := p1 <-> p2.
  Instance equiv_Equiv : Equivalence equiv.
  firstorder.
  Qed.

  Infix "==" := equiv (at level 90).

  Definition or : B -> B -> B.
    intros p1 p2.
    refine {| P := p1 \/ p2; |}.
    destruct (dec p1); eauto.
    destruct (dec p2); eauto.
    right; tauto.
  Defined.

  Definition and : B -> B -> B.
    intros p1 p2.
    refine {| P := p1 /\ p2; |}.
    destruct (dec p1); try tauto.
    destruct (dec p2); try tauto.
  Defined.

  Definition not: B -> B.
    intros p.
    refine {| P := ~p |}.
    destruct (dec p); eauto.
  Defined.

  Instance or_respects_equiv : Proper (equiv ==> equiv ==> equiv) or.
  Proof.
    unfold Proper, equiv, respectful; simpl; intuition auto.
  Qed.

  Instance and_respects_equiv : Proper (equiv ==> equiv ==> equiv) and.
  Proof.
    unfold Proper, equiv, respectful; simpl; intuition auto.
  Qed.

  Instance not_respects_equiv : Proper (equiv ==> equiv) not.
  Proof.
    unfold Proper, equiv, respectful; simpl; intuition auto.
  Qed.

  Definition zero : B := {| P := False;
                            dec := right (fun x => x) |}.
  Definition one : B := {| P := True;
                           dec := left I |}.

  Module BANotations.
    Infix "+" := or.
    Infix "*" := and.
    Notation "! x" := (not x) (at level 10, format "! x").
    Notation "0" := zero.
    Notation "1" := one.
  End BANotations.
  Import BANotations.

  Section Laws.
    Context (a b c:B).

    Ltac ba_solve :=
      unfold equiv, and, or, not; simpl; tauto.

    Notation magic := ltac:(ba_solve).

    Definition or_assoc : a + (b + c) == a + b + c := magic.
    Definition or_comm : a + b == b + a := magic.
    Definition or_zero : a + 0 == a := magic.
    Definition or_one : a + 1 == 1 := magic.
    Definition or_absorption : a + a == a := magic.
    Definition and_or_distr : a*(b + c) == a*b + a*c := magic.
    Definition not_or_distr : !(a + b) == !a * !b := magic.

    Definition zero_dual : !0 == 1 := magic.
    Definition one_dual : !1 == 0 := magic.
    Theorem double_neg : !(!a) == a.
    Proof.
      unfold equiv, and, or, not; simpl.
      split; auto.
    Qed.
  End Laws.
End DecidableProp.
