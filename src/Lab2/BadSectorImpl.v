Require Import POCS.
Require Import BadSectorAPI.


Extraction Language Haskell.

Module BadSectorDisk <: BadSectorAPI.

  Axiom init : proc InitResult.
  Axiom read : addr -> proc block.
  Axiom write : addr -> block -> proc unit.
  Axiom getBadSector : proc addr.
  Axiom size : proc nat.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
  Axiom write_ok : forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
  Axiom getBadSector_ok : proc_spec getBadSector_spec getBadSector recover abstr.
  Axiom size_ok : proc_spec size_spec size recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_wipe.

End BadSectorDisk.

Extract Constant BadSectorDisk.read => "BadSectorDisk.Ops.read".
Extract Constant BadSectorDisk.write => "BadSectorDisk.Ops.write".
Extract Constant BadSectorDisk.getBadSector => "BadSectorDisk.Ops.getBadSector".
Extract Constant BadSectorDisk.size => "BadSectorDisk.Ops.size".
