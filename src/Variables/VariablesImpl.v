Require Import Automation.

Require Import Variables.VariablesAPI.
Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.

Axiom read : Vars.var -> prog nat.
Axiom write : Vars.var -> nat -> prog unit.

Module Vars.

  Definition vars_op_impl T (op: Vars.Op T) : prog T :=
    match op with
    | Vars.Read v => read v
    | Vars.Write v val => write v val
    end.

  Definition impl : InterfaceImpl Vars.Op :=
    {| op_impl := vars_op_impl;
       recover_impl := Ret tt;
       init_impl := Ret Initialized; |}.

  Axiom abstr : Abstraction Vars.State.

  Axiom impl_ok :  forall (T : Type) (op : Vars.Op T),
      prog_spec (op_spec Vars.API op) (op_impl impl T op)
                (recover_impl impl) abstr.

  Axiom init_ok : init_invariant (init_impl impl) (recover_impl impl) abstr.

  Axiom vars_wipe_world_abstraction : forall w state,
      abstraction abstr (world_crash w) state <->
      abstraction abstr w state.

  Hint Resolve -> vars_wipe_world_abstraction.
  Hint Resolve <- vars_wipe_world_abstraction.

  Theorem vars_crash_ok : wipe_valid abstr Vars.wipe.
  Proof.
    constructor; simpl; unfold Vars.wipe;
      intros; subst; eauto.
  Qed.

  Definition vars : Interface Vars.API.
    unshelve econstructor.
    - exact impl.
    - exact abstr.
    - apply impl_ok.
    - unfold rec_noop; simpl; intros.
      unfold prog_spec; simpl; intros.
      inv_rexec; inv_ret; eauto.
      remember (world_crash w').
      generalize dependent w'.
      unfold Vars.wipe.
      induction H3; intros; inv_exec; eauto.
    - apply init_ok.
  Defined.

End Vars.
