Require Import POCS.

Module RemappedDisk.

  Inductive Op : Type -> Type :=
  | Read (a:addr) : Op block
  | Write (a:addr) (b:block) : Op unit
  | DiskSize : Op nat.

  Definition State := disk.

  (* help out type inference *)
  Implicit Type (state:State).

  Inductive step : forall `(op: Op T), Semantics State T :=
  | step_read : forall a r (d : disk),
      d a = Some r \/ d a = None ->
      step (Read a) d r d
  | step_write : forall a b (d : disk),
      step (Write a b) d tt (diskUpd d a b)
  | step_size : forall d r,
      r = size d ->
      step DiskSize d r d.

  Definition crash_relation state state' := False.
  Definition bg_step state state' := state = state'.
  Definition inited state := True.

  Definition API : InterfaceAPI Op State :=
    {|
      op_sem := @step;
      crash_effect := crash_relation;
      init_sem := inited;
    |}.

End RemappedDisk.
