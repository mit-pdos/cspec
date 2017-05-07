Require Import Prog.
Require Import Disk.

(* Defines programs over a single disk. *)

Module D.

  Inductive Op : Type -> Type :=
  | Read (a:addr) : Op block
  | Write (a:addr) (b:block) : Op unit
  | DiskSize : Op nat.

  Definition prog := Prog.prog Op.

  Definition State := disk.

  Inductive step : Semantics Op State :=
  | step_read : forall a r (state: State),
      (forall b, state a = Some b -> r = b) ->
      step (Read a) state r state
  | step_write : forall a b (state: State),
      step (Write a b) state tt (diskUpd state a b)
  | step_disk_size : forall (state: State),
      step (DiskSize) state (size state) state.

  Definition exec := Prog.exec step.
  Definition exec_recover := Prog.exec_recover step.

End D.
