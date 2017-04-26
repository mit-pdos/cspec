Require Import Refinement.IO.
Require Import TwoDiskAPI.
Require Import Implements.

(* TD is an implementation of the operations described in TDSpec.

 We don't actually implement this layer, instead assuming some operations exist
 that will be filled in later in the extracted code. *)
Module TD.

  Axiom Read : diskId -> addr -> IO block.
  Axiom Write : diskId -> addr -> block -> IO unit.

  Axiom abstraction : world -> TDSpec.State.

  Axiom Read_spec : forall i a,
      implements
        (TDSpec.Read i a)
        (io_semantics (Read i a))
        abstraction.

  Axiom Write_spec : forall i a b,
      implements
        (TDSpec.Write i a b)
        (io_semantics (Write i a b))
        abstraction.

End TD.
