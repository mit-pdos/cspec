Require Import Prog.
Require Import Automation.

Require Import Disk.AsyncDisk.
Require Export TwoDisk.TwoDiskDefs.
Require Import Refinement.Interface.

Module TD.

  Import TwoDiskDefs.TD.

  (* shadow state with a specialized version for async disks *)
  Definition State := TD.State disk.

  (* help out type inference *)
  Implicit Type (state:State).

  Definition bg_step state state'' :=
    exists state', bg_failure state state' /\
          disks_rel pflushed state state'.

  Inductive op_step : forall `(op: Op T), Semantics State T :=
  | step_read : forall a i r state,
      match get_disk i state with
      | Some d => match d a with
                 | Some b0 => r = Working (latest b0)
                 | None => exists b, r = Working b
                 end
      | None => r = Failed
      end ->
      op_step (Read i a) state r state
  | step_write : forall a i b state r state',
      match get_disk i state with
      | Some d => match d a with
                 | Some bs0 => state' = set_disk i state (diskUpd d a (buffer b bs0))
                 | None => state' = state
                 end /\
                 r = Working tt
      | None => r = Failed /\ state' = state
      end ->
      op_step (Write i a b) state r state'
  | step_sync : forall i state r state',
      match get_disk i state with
      | Some d => state' = set_disk i state (flush d) /\
                 r = Working tt
      | None => state' = state /\
               r = Failed
      end ->
      op_step (Sync i) state r state'
  | step_size : forall i state r,
      match get_disk i state with
      | Some d => r = Working (size d)
      | None => r = Failed
      end ->
      op_step (DiskSize i) state r state.

  Definition wipe state := state.

  Definition API : InterfaceAPI Op State :=
    background_step bg_step (@op_step) wipe.

  Ltac inv_step :=
    match goal with
    | [ H: op_step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      repeat sigT_eq;
      safe_intuition
    end.

End TD.
