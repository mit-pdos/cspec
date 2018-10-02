Require Import PeanoNat.
Require Import Permutation.

Set Implicit Arguments.

Class Default A := default_val: A.

Instance def_f A B {def:Default B} : Default (A -> B) := fun _ => default_val.
Instance def_pair A B {defA:Default A} {defB:Default B}
  : Default (A*B) := (default_val, default_val).
Instance def_type : Default Type := unit.

Hint Extern 1 (Default _) => solve [ constructor ] : typeclass_instances.

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
