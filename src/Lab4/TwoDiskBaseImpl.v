Require Import POCS.
Require Import TwoDiskBaseAPI.


Extraction Language Haskell.

Module TwoDiskBase <: TwoDiskBaseAPI.

  Axiom init : prog InitResult.
  Axiom read : diskId -> addr -> prog (DiskResult block).
  Axiom write : diskId -> addr -> block -> prog (DiskResult unit).
  Axiom size : diskId -> prog (DiskResult nat).
  Axiom recover : prog unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall i a, prog_spec (op_spec (combined_step (op_read i a))) (read i a) recover abstr.
  Axiom write_ok : forall i a b, prog_spec (op_spec (combined_step (op_write i a b))) (write i a b) recover abstr.
  Axiom size_ok : forall i, prog_spec (op_spec (combined_step (op_size i))) (size i) recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_wipe.

End TwoDiskBase.

Extract Constant TwoDiskBase.read => "TD.read".
Extract Constant TwoDiskBase.write => "TD.write".
Extract Constant TwoDiskBase.size => "TD.size".
