Require Import Disk.

Require Import Shallow.TwoDiskAPI.
Require Import Shallow.Interface.
Require Import Shallow.ProgLang.Prog.
Require Import
        Shallow.ProgLang.Hoare
        Shallow.ProgLang.HoareRecovery.

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
       recover_impl := Ret tt; |}.

  Axiom refinement : Refinement TD.State.

  Axiom impl_ok :  forall (T : Type) (op : TD.Op T),
      prog_rspec (op_spec TD.API op) (op_impl impl T op)
                 (recover_impl impl) refinement.

  Definition td : Interface TD.API.
    unshelve econstructor.
    - exact impl.
    - exact refinement.
    - apply impl_ok.
    - unfold rec_noop; simpl; intros.
      unfold prog_rspec; simpl; intros.
      inv_rexec; inv_exec; eauto.
      induction H3; inv_exec; eauto.
  Defined.

End TD.
