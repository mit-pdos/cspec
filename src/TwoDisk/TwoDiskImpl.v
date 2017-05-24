Require Import Disk.

Require Import TwoDisk.TwoDiskAPI.
Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.

Module TD.
  Axiom read : diskId -> addr -> prog (DiskResult block).
  Axiom write : diskId -> addr -> block -> prog (DiskResult unit).
  Axiom diskSize : diskId -> prog (DiskResult nat).

  Definition td_op_impl T (op: TD.Op T) : prog T :=
    match op with
    | TD.Read d a => read d a
    | TD.Write d a b => write d a b
    | TD.DiskSize d => diskSize d
    end.

  Definition impl : InterfaceImpl TD.Op :=
    {| op_impl := td_op_impl;
       recover_impl := Ret tt;
       init_impl := Ret Initialized; |}.

  Axiom refinement : Refinement TD.State.

  Axiom impl_ok :  forall (T : Type) (op : TD.Op T),
      prog_spec (op_spec TD.API op) (op_impl impl T op)
                (recover_impl impl) refinement.

  Axiom init_ok : init_invariant (init_impl impl) (recover_impl impl) refinement.

  Definition td : Interface TD.API.
    unshelve econstructor.
    - exact impl.
    - exact refinement.
    - apply impl_ok.
    - unfold rec_noop; simpl; intros.
      unfold prog_spec; simpl; intros.
      inv_rexec; inv_ret; eauto.
      induction H3; inv_exec; eauto.
    - apply init_ok.
  Defined.

End TD.
