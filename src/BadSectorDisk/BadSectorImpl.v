Require Import POCS.
Require Import BadSectorAPI.


Extraction Language Haskell.

Module BadSectorDisk <: BadSectorAPI.

  Axiom init : prog InitResult.
  Axiom read : addr -> prog block.
  Axiom write : addr -> block -> prog unit.
  Axiom getBadSector : prog addr.
  Axiom diskSize : prog nat.
  Axiom recover : prog unit.

  Axiom abstr : Abstraction State.

  Axiom read_ok : forall a, prog_spec (read_spec a) (read a) recover abstr.
  Axiom write_ok : forall a v, prog_spec (write_spec a v) (write a v) recover abstr.
  Axiom getBadSector_ok : prog_spec getBadSector_spec getBadSector recover abstr.
  Axiom diskSize_ok : prog_spec diskSize_spec diskSize recover abstr.
  Axiom recover_noop : rec_noop recover abstr wipe.

End BadSectorDisk.

Extract Constant BadSectorDisk.read => "BadSectorDisk.Ops.read".
Extract Constant BadSectorDisk.write => "BadSectorDisk.Ops.write".
Extract Constant BadSectorDisk.getBadSector => "BadSectorDisk.Ops.getBadSector".
Extract Constant BadSectorDisk.diskSize => "BadSectorDisk.Ops.diskSize".
