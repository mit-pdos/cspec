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
      | Some d => state' = set_disk i state (diskUpdF d a (buffer b)) /\
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

  Definition wipe state := disks_map oldest state.

  Definition API : InterfaceAPI Op State :=
    {| op_sem := post_step (pre_step bg_failure (@op_step))
                           (disks_rel pflushed);
       crash_effect := wipe; |}.

  Ltac inv_step :=
    match goal with
    | [ H: op_step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      repeat sigT_eq;
      safe_intuition
    end.

  Ltac inv_failure :=
    match goal with
    | [ H: bg_failure _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

End TD.
