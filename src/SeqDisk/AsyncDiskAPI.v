Require Import Prog.
Require Import Disk.AsyncDisk.

Require Export SeqDisk.SeqDiskDefs.
Require Import Refinement.Interface.

(* Defines programs over a single, asynchronous disk. *)

Module D.

  Import SeqDiskDefs.D.

  Definition State := disk.

  Definition wipe : State -> State := wipeDisk.

  Inductive step : forall `(op: Op T), Semantics State T :=
  | step_read : forall a r (state: State),
      (forall b, state a = Some b -> r = curr_val b) ->
      step (Read a) state r state
  | step_write : forall a b (state: State),
      step (Write a b) state tt (diskUpdF state a (buffer b))
  | step_sync : forall (state: State),
      step (Sync) state tt (flush state)
  | step_disk_size : forall (state: State),
      step (DiskSize) state (size state) state.

  Definition API := {| op_sem := post_step (@step) pflush;
                       crash_effect := wipe; |}.

End D.
