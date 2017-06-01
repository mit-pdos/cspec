Require Import Prog.
Require Import Disk.SimpleDisk.

Require Export SeqDisk.SeqDiskDefs.
Require Import Refinement.Interface.

(* Defines programs over a single disk. *)

Module D.

  Import SeqDiskDefs.D.

  Definition State := disk.

  Inductive step : forall `(op: Op T), Semantics State T :=
  | step_read : forall a r (state: State),
      (forall b, state a = Some b -> r = b) ->
      step (Read a) state r state
  | step_write : forall a b (state: State),
      step (Write a b) state tt (diskUpd state a b)
  | step_sync : forall (state: State),
      (* synchronous sync is a no-op *)
      step (Sync) state tt state
  | step_disk_size : forall (state: State),
      step (DiskSize) state (size state) state.

  Definition API := {| op_sem := @step;
                       crash_effect := fun state state' => state' = state; |}.

End D.
