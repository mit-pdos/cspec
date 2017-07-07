Require Import Disk.SimpleDisk.
Require Import BadSectorDisk.BadSectorAPI.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import Refinement.Interface.

Import BadSectorDisk.
Module BadSectorDisk.

  Axiom hs_read : addr -> prog block.
  Axiom hs_write : addr -> block -> prog unit.
  Axiom hs_getBadSector : prog addr.
  Axiom hs_diskSize : prog nat.

  Definition badsector_op_impl T (op: Op T) : prog T :=
    match op with
    | Read a => hs_read a
    | Write a b => hs_write a b
    | GetBadSector => hs_getBadSector
    | DiskSize => hs_diskSize
    end.

  Definition impl : InterfaceImpl Op :=
    {|
      op_impl := badsector_op_impl;
      recover_impl := Ret tt;
      init_impl := Ret Initialized;
    |}.

  Axiom abstr : Abstraction State.

  Axiom impl_ok :  forall (T : Type) (op : Op T),
      prog_spec (op_spec API op) (op_impl impl T op)
                (recover_impl impl) abstr.
  Axiom init_ok : init_invariant (init_impl impl) (recover_impl impl) abstr inited.
  Axiom recover_ok : rec_noop (recover_impl impl) abstr (crash_effect API).

  Definition bs : Interface API.
    unshelve econstructor.
    - exact impl.
    - exact abstr.
    - apply impl_ok.
    - apply recover_ok.
    - apply init_ok.
  Defined.

End BadSectorDisk.

Extraction Language Haskell.

Extract Constant BadSectorDisk.hs_read => "BadSector.read".
Extract Constant BadSectorDisk.hs_write => "BadSector.write".
Extract Constant BadSectorDisk.hs_getBadSector => "BadSector.getBadSector".
Extract Constant BadSectorDisk.hs_diskSize => "BadSector.diskSize".
Extract Constant BadSectorDisk.abstr => "Hoare.Build_LayerAbstraction".
