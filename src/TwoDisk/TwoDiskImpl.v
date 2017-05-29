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

  Axiom refinement : Refinement TD.State.

  Axiom impl_ok :  forall (T : Type) (op : TD.Op T),
      prog_spec (op_spec TD.API op) (op_impl impl T op)
                (recover_impl impl) refinement.

  Axiom init_ok : init_invariant (init_impl impl) (recover_impl impl) refinement.

  Axiom td_wipe_world_abstraction : forall w,
      abstraction refinement (world_crash w) = abstraction refinement w.

  Theorem td_crash_ok : wipe_valid refinement TD.wipe.
  Proof.
    constructor; simpl; unfold TD.wipe;
      eauto using td_wipe_world_abstraction.
  Qed.

  Axiom invariant_under_crashes : forall w, invariant refinement w ->
                                       invariant refinement (world_crash w).

  Hint Resolve invariant_under_crashes.

  Definition td : Interface TD.API.
    unshelve econstructor.
    - exact impl.
    - exact refinement.
    - apply impl_ok.
    - unfold rec_noop; simpl; intros.
      unfold prog_spec; simpl; intros.
      inv_rexec; inv_ret; eauto.
      remember (world_crash w').
      generalize dependent w'.
      induction H3; intros; inv_exec.
      rewrite ?(wipe_abstraction td_crash_ok) in *;
        unfold TD.wipe; eauto.
      specialize (IHexec_recover (world_crash w'0)).
      rewrite ?(wipe_abstraction td_crash_ok) in *;
        unfold TD.wipe in *.
      safe_intuition eauto.
    - apply init_ok.
    - apply td_crash_ok.
  Defined.

End TD.
