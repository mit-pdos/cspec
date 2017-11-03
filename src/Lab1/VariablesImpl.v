Require Import POCS.
Require Import VariablesAPI.

(** * An implementation of Variables.

  This implementation is in Haskell and we assume it is correct.
 *)

Extraction Language Haskell.

(*
Extract Constant Vars.init => "Variables.Ops.init".
Extract Constant Vars.read => "Variables.Ops.read".
Extract Constant Vars.write => "Variables.Ops.write".
*)
