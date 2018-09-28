Require Import RelationClasses.
Require Import Helpers.Setoid.
Require Import Morphisms.
Require Import Varmap.

Unset Intuition Negation Unfolding.
Set Implicit Arguments.

Class BA_Ops {B:Setoid} :=
  { or: B -> B -> B;
    and : B -> B -> B;
    not: B -> B;
    zero: B;
    one: B;
  }.

Module BANotations.
  Infix "+" := or.
  Infix "*" := and.
  Notation "! x" := (not x) (at level 10, format "! x").
  Notation "0" := zero.
  Notation "1" := one.
End BANotations.
Import BANotations.

Generalizable Variables B.

Class BooleanAlgebra `{BAo: BA_Ops B} :=
  {
    or_respects_equiv :> Proper (equiv ==> equiv ==> equiv) or;
    or_assoc : forall a b c, a + (b + c) == a + b + c;
    or_comm : forall a b, a + b == b + a;
    or_zero : forall a, a + 0 == a;
    or_one : forall a, a + 1 == 1;
    or_absorption : forall a, a + a == a;

    and_respects_equiv :> Proper (equiv ==> equiv ==> equiv) and;
    and_or_distr : forall a b c, a*(b + c) == a*b + a*c;
    not_or_distr : forall a b, !(a + b) == !a * !b;

    not_respects_equiv :> Proper (equiv ==> equiv) not;
    zero_dual : !0 == 1;
    one_dual : !1 == 0;
    double_neg : forall a, !(!a) == a;
  }.

Section BAFacts.
  Context `{BAo: BA_Ops B}.
  Context {BA: BooleanAlgebra}.

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
    rewrite ?double_neg in H; auto.
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
    constr:(interpret ctx x).

  Ltac quote term rx :=
    let reified := quote_with (varmap.empty B) term in
    rx reified.

  Ltac quote_eqn :=
    match goal with
    | |- ?x == ?y =>
      quote x ltac:(fun x' =>
                      match x' with
                      | interpret ?ctx ?xt =>
                        let y' := quote_with ctx y in
                        match y' with
                        | interpret ?ctx' ?yt =>
                          change (interpret ctx' xt == interpret ctx' yt)
                        end
                      end)
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

Module BoolAlgebra : BooleanAlgebra.
  Definition B:Type := bool.
  Definition equiv: B -> B -> Prop := eq.
  Instance equiv_Equiv : Equivalence equiv.
  typeclasses eauto.
  Qed.

  Infix "==" := equiv (at level 90).

  Definition or: B -> B -> B := orb.
  Definition and : B -> B -> B := andb.
  Definition not: B -> B := negb.

  Instance or_respects_equiv : Proper (equiv ==> equiv ==> equiv) or.
  congruence.
  Qed.
  Instance and_respects_equiv : Proper (equiv ==> equiv ==> equiv) and.
  congruence.
  Qed.
  Instance not_respects_equiv : Proper (equiv ==> equiv) not.
  congruence.
  Qed.

  Definition zero : B := false.
  Definition one : B := true.

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
      (* clear unmentioned section variables to ensure theorem does not depend
      on them *)
      repeat match goal with
             | [ b: B |- _ ] =>
               match goal with
               | |- context[b] => idtac
               | |- _ => clear b
               end
             end;
      unfold or, and, not, equiv, zero, one;
      repeat match goal with
             | _ => reflexivity
             | [ b: B |- _ ] => destruct b; clear b; simpl
             end.

    Notation magic := ltac:(ba_solve) (only parsing).

    Definition or_assoc : a + (b + c) == a + b + c := magic.
    Definition or_comm : a + b == b + a := magic.
    Definition or_zero : a + 0 == a := magic.
    Definition or_one : a + 1 == 1 := magic.
    Definition or_absorption : a + a == a := magic.
    Definition and_or_distr : a*(b + c) == a*b + a*c := magic.
    Definition not_or_distr : !(a + b) == !a * !b := magic.

    Definition zero_dual : !0 == 1 := magic.
    Definition one_dual : !1 == 0 := magic.
    Definition double_neg : !(!a) == a := magic.
  End Laws.
End BoolAlgebra.
