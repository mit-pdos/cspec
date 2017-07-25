Require Import POCS.

Module AtomicPair.

  Inductive Op : Type -> Type :=
  | Get : Op (block*block)
  | Put (p : block*block) : Op unit.

  Definition State : Type := block*block.

  (* help out type inference *)
  Implicit Type (state:State).

  Inductive step : forall `(op: Op T), Semantics State T :=
  | step_get : forall s r,
      s = r ->
      step (Get) s r s
  | step_put : forall s v,
      step (Put v) s tt v.

  Definition crash_relation state state' := state' = state.
  Definition inited state := True.

  Definition API : InterfaceAPI Op State :=
    {|
      op_sem := @step;
      crash_effect := crash_relation;
      init_sem := inited;
    |}.

End AtomicPair.
