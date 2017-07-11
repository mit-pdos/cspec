Require Import POCS.

Module RemappedDisk.

  Inductive Op : Type -> Type :=
  | Read (a:addr) : Op block
  | Write (a:addr) (b:block) : Op unit
  | DiskSize : Op nat.

  Definition State := disk.

  (* help out type inference *)
  Implicit Type (state:State).

  Inductive op_step : forall `(op: Op T), Semantics State T :=
  | step_read : forall a r (d : disk),
      d a = Some r \/ d a = None ->
      op_step (Read a) d r d
  | step_write : forall a b (d : disk),
      op_step (Write a b) d tt (diskUpd d a b)
  | step_size : forall d,
      op_step DiskSize d (size d) d.

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

End RemappedDisk.
