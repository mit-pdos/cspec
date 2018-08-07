(** This file exports the entire CSPEC framework as one import. *)

(* TODO: we could probably export a lot less from each of these files, to
clarify what the framework provides vs internal proofs. *)

Require Export List.
Require Export Omega.

Require Export Helpers.ProofAutomation.
Require Export Helpers.Instances.
Require Export Helpers.ListStuff.
Require Export Helpers.Sets.
Require Export Helpers.Maps.
Require Export Helpers.Ordering.
Require Export Helpers.StringUtils.
Require Export Helpers.RecordSet.

Require Export Spec.ConcurExec.
Require Export Spec.Compile.
Require Export Spec.Abstraction.
Require Export Spec.Modules.
Require Export Spec.Movers.
Require Export Spec.Protocol.
Require Export Spec.CompileLoop.
Require Export Spec.Horizontal.
Require Export Spec.Equiv.
Require Export Spec.CodeOpt.
