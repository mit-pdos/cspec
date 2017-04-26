Require Export Disk.
Require Import Implements.

Module DSpec.
  Record State :=
    Disk { sdisk : disk }.

  Definition Read a : Semantics block :=
    StepRel (fun state r state' =>
               match sdisk state a with
               | Some v0 => r = v0
               | None => True
               end /\ state' = state).

  Definition Write a b : Semantics unit :=
    StepRel (fun state r state' =>
               match sdisk state a with
               | Some v0 => state' = Disk (upd (sdisk state) a b) /\
                           r = tt
               | None => True
               end).

End DSpec.

(* Local Variables: *)
(* company-coq-local-symbols: (("State" . ?Σ) ("state" . ?σ) ("state'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
