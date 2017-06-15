Require Import Automation.
Require Import Disk.SimpleDisk.

Require Import TwoDisk.TwoDiskAPI.
Require Import TwoDisk.TwoDiskOps.
Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.

Module TD.

  Definition td_op_impl T (op: TD.Op T) : prog T :=
    match op with
    | TD.Read d a => read d a
    | TD.Write d a b => write d a b
    | TD.Sync d => sync d
    | TD.DiskSize d => diskSize d
    end.

  Definition impl : InterfaceImpl TD.Op :=
    {| op_impl := td_op_impl;
       recover_impl := Ret tt;
       init_impl := Ret Initialized; |}.

  Axiom abstr : Abstraction TD.State.

  Axiom impl_ok :  forall (T : Type) (op : TD.Op T),
      prog_spec (op_spec TD.API op) (op_impl impl T op)
                (recover_impl impl) abstr.

  Axiom init_ok : init_invariant (init_impl impl) (recover_impl impl) abstr TD.inited.

  Axiom td_wipe_world_abstraction : forall w state,
      abstraction abstr (world_crash w) state <->
      abstraction abstr w state.

  Hint Resolve -> td_wipe_world_abstraction.
  Hint Resolve <- td_wipe_world_abstraction.

  Theorem td_crash_ok : wipe_valid abstr TD.wipe.
  Proof.
    constructor; simpl; unfold TD.wipe;
      intros; subst; eauto.
  Qed.

  Definition td : Interface TD.API.
    unshelve econstructor.
    - exact impl.
    - exact abstr.
    - apply impl_ok.
    - unfold rec_noop; simpl; intros.
      unfold prog_spec; simpl; intros.
      inv_rexec; inv_ret; eauto.
      remember (world_crash w').
      generalize dependent w'.
      unfold TD.wipe.
      induction H3; intros; inv_exec; eauto.
    - apply init_ok.
  Defined.

End TD.
