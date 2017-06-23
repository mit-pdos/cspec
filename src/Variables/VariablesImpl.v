Require Import Automation.

Require Import Variables.VariablesAPI.
Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import Refinement.ProgLang.NoCrashes.

Module Vars.

  Axiom read : Vars.var -> prog nat.
  Axiom write : Vars.var -> nat -> prog unit.

  Definition vars_op_impl T (op: Vars.Op T) : prog T :=
    match op with
    | Vars.Read v => read v
    | Vars.Write v val => write v val
    end.

  Definition impl : InterfaceImpl Vars.Op :=
    {|
      op_impl := vars_op_impl;
      recover_impl := Ret tt;
      init_impl := Ret Initialized;
    |}.

  Axiom abstr : Abstraction Vars.State.

  Axiom impl_ok :  forall (T : Type) (op : Vars.Op T),
      prog_spec (op_spec Vars.API op) (op_impl impl T op)
                (recover_impl impl) abstr.

  Axiom init_ok : init_invariant (init_impl impl) (recover_impl impl) abstr Vars.inited.

  Definition vars : Interface Vars.API.
    unshelve econstructor.
    - exact impl.
    - exact abstr.
    - apply impl_ok.
    - cannot_crash.
    - apply init_ok.
  Defined.

End Vars.
