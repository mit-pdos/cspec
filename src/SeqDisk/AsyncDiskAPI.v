Require Import Prog.
Require Import Disk.AsyncDisk.

Require Export SeqDisk.SeqDiskDefs.
Require Import Refinement.Interface.

(* Defines programs over a single, asynchronous disk. *)

Module D.

  Import SeqDiskDefs.D.

  Definition State := histdisk.

  Definition wipe : State -> State -> Prop := wipeHist.

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

  Definition inited (state: State) := True.

  Definition API :=
    {|
      op_sem := @step;
      crash_effect := wipe;
      init_sem := inited;
    |}.

End D.
