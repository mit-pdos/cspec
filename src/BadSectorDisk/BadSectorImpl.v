Require Import Automation.
Require Import Disk.SimpleDisk.

Require Import BadSectorDisk.BadSectorAPI.
Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.

Axiom read : addr -> prog block.
Axiom write : addr -> block -> prog unit.
Axiom getBadSector : prog addr.
Axiom diskSize : prog nat.

Module BadSectorDisk.

  Definition bs_op_impl T (op: BadSectorDisk.Op T) : prog T :=
    match op with
    | BadSectorDisk.Read a => read a
    | BadSectorDisk.Write a b => write a b
    | BadSectorDisk.GetBadSector => getBadSector
    | BadSectorDisk.DiskSize => diskSize
    end.

  Definition impl : InterfaceImpl BadSectorDisk.Op :=
    {| op_impl := bs_op_impl;
       recover_impl := Ret tt;
       init_impl := Ret Initialized; |}.

  Axiom refinement : Refinement BadSectorDisk.State.

  Axiom impl_ok :  forall (T : Type) (op : BadSectorDisk.Op T),
      prog_spec (op_spec BadSectorDisk.API op) (op_impl impl T op)
                (recover_impl impl) refinement.

  Axiom init_ok : init_invariant (init_impl impl) (recover_impl impl) refinement.

  Definition bs : Interface BadSectorDisk.API.
    unshelve econstructor.
    - exact impl.
    - exact refinement.
    - apply impl_ok.
    - unfold rec_noop; simpl; intros.
      unfold prog_spec; simpl; intros.
      inv_rexec; inv_ret; eauto.
      admit.
    - apply init_ok.
  Admitted.

End BadSectorDisk.
