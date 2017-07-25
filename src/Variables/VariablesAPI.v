Require Import POCS.

Module Vars.

  Inductive var :=
  | VarCount
  | VarSum.

  Inductive Op : Type -> Type :=
  | Read (v : var) : Op nat
  | Write (v : var) (val : nat) : Op unit.

  (** The state the program manipulates as it executes. *)
  Record State := mkState {
    StateCount : nat;
    StateSum : nat;
  }.

  Instance var_dec : EqualDec var.
    unfold EqualDec; intros.
    destruct x; destruct y;
      try (left; congruence);
      try (right; congruence).
  Defined.

  (* help out type inference *)
  Implicit Type (state:State).

  Inductive op_step : forall `(op: Op T), Semantics State T :=
  | step_read_count : forall r state,
      StateCount state = r ->
      op_step (Read VarCount) state r state
  | step_read_sum : forall r state,
      StateSum state = r ->
      op_step (Read VarSum) state r state
  | step_write_count : forall val state,
      op_step (Write VarCount val) state tt (mkState val (StateSum state))
  | step_write_sum : forall val state,
      op_step (Write VarSum val) state tt (mkState (StateCount state) val).

  Definition crash_relation state state' := False.
  Definition inited state := True.

  Definition API : InterfaceAPI Op State :=
    {|
      op_sem := @op_step;
      crash_effect := crash_relation;
      init_sem := inited;
    |}.

  Ltac inv_step :=
    idtac;  (* Ltac evaluation order issue when passing tactics *)
    match goal with
    | [ H: op_step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      repeat sigT_eq;
      safe_intuition
    end.

End Vars.
