Require Import POCS.
Require Import OneDisk.OneDiskAPI.

Import OneDisk.
Module OneDisk.

  Axiom hs_read : addr -> prog block.
  Axiom hs_write : addr -> block -> prog unit.
  Axiom hs_diskSize : prog nat.

  Definition onedisk_op_impl T (op: Op T) : prog T :=
    match op with
    | Read a => hs_read a
    | Write a b => hs_write a b
    | DiskSize => hs_diskSize
    end.

  Definition impl : InterfaceImpl Op :=
    {|
      op_impl := onedisk_op_impl;
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

End OneDisk.

Extraction Language Haskell.

Extract Constant OneDisk.hs_read => "OneDisk.Ops.read".
Extract Constant OneDisk.hs_write => "OneDisk.Ops.write".
Extract Constant OneDisk.hs_diskSize => "OneDisk.Ops.diskSize".
Extract Constant OneDisk.abstr => "Hoare.Build_LayerAbstraction".
