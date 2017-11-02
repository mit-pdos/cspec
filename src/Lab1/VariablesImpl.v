Require Import POCS.
Require Import VariablesAPI.

(** * An implementation of Variables.

  This implementation is in Haskell and we assume it is correct.
 *)

Extraction Language Haskell.

Module Vars <: VarsAPI.

  Axiom init : proc InitResult.
  Axiom read : var -> proc nat.
  Axiom write : var -> nat -> proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init abstr inited_any.
  Axiom read_ok : forall v, proc_spec (read_spec v) (read v) abstr.
  Axiom write_ok : forall v val, proc_spec (write_spec v val) (write v val) abstr.

End Vars.

Extract Constant Vars.init => "Variables.Ops.init".
Extract Constant Vars.read => "Variables.Ops.read".
Extract Constant Vars.write => "Variables.Ops.write".
