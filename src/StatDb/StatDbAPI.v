Require Import POCS.
Require Import Refinement.Interface.

Module StatDB.

  Inductive Op : Type -> Type :=
  | Add (v : nat) : Op unit
  | Mean : Op (option nat).

  Definition State := list nat.

  Inductive step : forall `(op: Op T), Semantics State T :=
  | step_add : forall v (state : State),
      step (Add v) state tt (v :: state)
  | step_mean_empty : forall (state : State),
      state = nil ->
      step Mean state None state
  | step_mean_nonempty : forall r (state : State),
      length state > 0 ->
      r = Nat.div (fold_right plus 0 state) (length state) ->
      step Mean state (Some r) state.

  Definition inited (state: State) := state = nil.
  Definition crash_relation (state state' : State) := False.

  Definition API :=
    {|
      op_sem := @step;
      crash_effect := crash_relation;
      init_sem := inited;
    |}.

End StatDB.
