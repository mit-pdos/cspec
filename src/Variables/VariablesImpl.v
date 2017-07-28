Require Import POCS.
Require Import VariablesAPI.


Extraction Language Haskell.

Axiom init : prog InitResult.
Axiom read : var -> prog nat.
Axiom write : var -> nat -> prog unit.
Axiom recover : prog unit.

Axiom abstr : Abstraction State.

Axiom read_ok : forall v, prog_spec (read_spec v) (read v) recover abstr.
Axiom write_ok : forall v val, prog_spec (write_spec v val) (write v val) recover abstr.
Axiom recover_noop : rec_noop recover abstr (@no_crash _).

Module Vars <: VarsAPI.

  Definition init := init.
  Definition read := read.
  Definition write := write.
  Definition recover := recover.

  Definition abstr := abstr.

  Definition read_ok := read_ok.
  Definition write_ok := write_ok.
  Definition recover_noop := recover_noop.

End Vars.

Extract Constant read => "Variables.read".
Extract Constant write => "Variables.write".
