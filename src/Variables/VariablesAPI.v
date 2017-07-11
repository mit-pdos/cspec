Require Import POCS.

Module Vars.

  Inductive var :=
  | VarCount
  | VarSum.

  Inductive Op : Type -> Type :=
  | Read (v : var) : Op nat
  | Write (v : var) (val : nat) : Op unit.

  (** The state the program manipulates as it executes. *)
  Definition State := mem var nat.

  Instance var_dec : EqualDec var.
    unfold EqualDec; intros.
    destruct x; destruct y;
      try (left; congruence);
      try (right; congruence).
  Defined.

  (* help out type inference *)
  Implicit Type (state:State).

  Inductive op_step : forall `(op: Op T), Semantics State T :=
  | step_read : forall v r state,
      state v = Some r ->
      op_step (Read v) state r state
  | step_write : forall v val state state',
      op_step (Write v val) state tt (upd state v val).

  Definition crash_relation state state' := False.
  Definition bg_step state state' := state = state'.
  Definition inited state := True.

  Definition API : InterfaceAPI Op State :=
    {|
      op_sem := pre_step bg_step (@op_step);
      crash_effect := crash_relation;
      init_sem := inited;
    |}.

  Ltac inv_step :=
    match goal with
    | [ H: op_step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      repeat sigT_eq;
      safe_intuition
    end.

  Ltac inv_bg :=
    match goal with
    | [ H: bg_step _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

End Vars.
