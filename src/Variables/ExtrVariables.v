Require Import POCS.
Require Import Variables.VariablesAPI.

Import Vars.
Module Vars.

  Axiom hs_read : var -> prog nat.
  Axiom hs_write : var -> nat -> prog unit.

  Definition vars_op_impl T (op: Op T) : prog T :=
    match op with
    | Read v => hs_read v
    | Write v x => hs_write v x
    end.

  Definition impl : InterfaceImpl Op :=
    {|
      op_impl := vars_op_impl;
      recover_impl := Ret tt;
      init_impl := Ret Initialized;
    |}.

  Axiom abstr : Abstraction State.

  Axiom impl_ok :  forall (T : Type) (op : Op T),
      prog_spec (op_spec API op) (op_impl impl T op)
                (recover_impl impl) abstr.
  Axiom init_ok : init_invariant (init_impl impl) (recover_impl impl) abstr inited.
  Axiom recover_ok : rec_noop (recover_impl impl) abstr (crash_effect API).

  Definition vars : Interface API.
    unshelve econstructor.
    - exact impl.
    - exact abstr.
    - apply impl_ok.
    - apply recover_ok.
    - apply init_ok.
  Defined.

End Vars.

Extraction Language Haskell.

Extract Constant Vars.hs_read => "Variables.read".
Extract Constant Vars.hs_write => "Variables.write".
Extract Constant Vars.abstr => "Hoare.Build_LayerAbstraction".
