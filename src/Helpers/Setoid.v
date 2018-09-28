Require Import Morphisms.
From Coq Require Export Setoid.

Record Setoid :=
  { T :> Type;
    equiv : relation T;
    equiv_Equiv : Equivalence equiv; }.

Arguments equiv {A} _ _ : rename.
Global Opaque equiv.

Existing Instance equiv_Equiv.

Infix "==" := equiv (at level 90).
