Require Import Implements.
Require Import TwoDiskAPI.

(* TD is an implementation of the operations described in TDSpec.

 We don't actually implement this layer, instead assuming some operations exist
 that will be filled in later in the extracted code. *)
Module TD.

  Axiom Read : diskId -> addr -> IO block.
  Axiom Write : diskId -> addr -> block -> IO unit.

  Axiom abstraction : world -> TDSpec.State.
  (* any world state, and thus any TD state that the abstraction function might
  produce, is ok, so we use a trivial invariant below *)

  Axiom Read_ok : forall i a,
      implements
        (TDSpec.Read i a)
        (Read i a)
        abstraction
        (fun _ => True).

  Axiom Write_ok : forall i a b,
      implements
        (TDSpec.Write i a b)
        (Write i a b)
        abstraction
        (fun _ => True).

End TD.
