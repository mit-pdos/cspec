Require Import POCS.
Require Import TwoDisk.TwoDiskAPI.

Module TD.

  Axiom hs_read : diskId -> addr -> prog (DiskResult block).
  Axiom hs_write : diskId -> addr -> block -> prog (DiskResult unit).
  Axiom hs_diskSize : diskId -> prog (DiskResult nat).

  Definition td_op_impl T (op: TD.Op T) : prog T :=
    match op with
    | TD.Read d a => hs_read d a
    | TD.Write d a b => hs_write d a b
    | TD.DiskSize d => hs_diskSize d
    end.

  Definition impl : InterfaceImpl TD.Op :=
    {|
      op_impl := td_op_impl;
      recover_impl := Ret tt;
      init_impl := Ret Initialized;
    |}.

  Axiom abstr : Abstraction TD.State.

  Axiom impl_ok :  forall (T : Type) (op : TD.Op T),
      prog_spec (op_spec TD.API op) (op_impl impl T op)
                (recover_impl impl) abstr.
  Axiom init_ok : init_invariant (init_impl impl) (recover_impl impl) abstr TD.inited.
  Axiom recover_ok : rec_noop (recover_impl impl) abstr (crash_effect TD.API).

  Definition td : Interface TD.API.
    unshelve econstructor.
    - exact impl.
    - exact abstr.
    - apply impl_ok.
    - apply recover_ok.
    - apply init_ok.
  Defined.

End TD.

Extraction Language Haskell.

Extract Constant TD.hs_read => "TD.read".
Extract Constant TD.hs_write => "TD.write".
Extract Constant TD.hs_diskSize => "TD.diskSize".
Extract Constant TD.abstr => "Hoare.Build_LayerAbstraction".
