Require Import POCS.
Require Import VariablesAPI.


Extraction Language Haskell.

Module Vars <: VarsAPI.

  Axiom init : prog InitResult.
  Axiom read : var -> prog nat.
  Axiom write : var -> nat -> prog unit.
  Axiom recover : prog unit.

  Axiom abstr : Abstraction State.

  Axiom read_ok : forall v, prog_spec (read_spec v) (read v) recover abstr.
  Axiom write_ok : forall v val, prog_spec (write_spec v val) (write v val) recover abstr.
  Axiom recover_noop : rec_noop recover abstr wipe.

End Vars.

Extract Constant Vars.read => "Variables.read".
Extract Constant Vars.write => "Variables.write".
