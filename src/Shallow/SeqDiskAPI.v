Require Import Prog.
Require Import Disk.

Require Import Shallow.Interface.

(* Defines programs over a single disk. *)

Module D.

  Inductive Op : Type -> Type :=
  | Read (a:addr) : Op block
  | Write (a:addr) (b:block) : Op unit
  | DiskSize : Op nat.

  Definition State := disk.

  Inductive step : forall `(op: Op T), Semantics State T :=
  | step_read : forall a r (state: State),
      (forall b, state a = Some b -> r = b) ->
      step (Read a) state r state
  | step_write : forall a b (state: State),
      step (Write a b) state tt (diskUpd state a b)
  | step_disk_size : forall (state: State),
      step (DiskSize) state (size state) state.

  Definition API := {| op_sem := @step |}.

End D.
