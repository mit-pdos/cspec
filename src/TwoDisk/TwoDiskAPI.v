Require Import Prog.
Require Import Automation.

Require Export TwoDisk.TwoDiskDefs.
Require Import Refinement.Interface.

Module TD.

  Inductive Op : Type -> Type :=
  | Read (i:diskId) (a:addr) : Op (DiskResult block)
  | Write (i:diskId) (a:addr) (b:block) : Op (DiskResult unit)
  (* get disk size in blocks *)
  | DiskSize (i:diskId) : Op (DiskResult nat).

  (** The state the program manipulates as it executes. *)
  Record State :=
    Disks { disk0 : option disk;
            disk1 : option disk;
            some_disk_works : disk0 = None -> disk1 = None -> False }.

  Arguments Disks disk0 disk1 some_disk_works : clear implicits.

  (** Get a particular disk from a state by id. *)
  Definition get_disk (i:diskId) (state:State) : option disk :=
    match i with
    | d0 => disk0 state
    | d1 => disk1 state
    end.

  Local Lemma d0_is_some (d_0: disk) (d_1: option disk) :
    Some d_0 = None -> d_1 = None -> False.
  Proof.
    congruence.
  Qed.

  Local Lemma d1_is_some (d_0: option disk) (d_1: disk) :
    d_0 = None -> Some d_1 = None -> False.
  Proof.
    congruence.
  Qed.

  Local Notation proof := (ltac:(first [ apply d0_is_some | apply d1_is_some ])) (only parsing).

  Definition set_disk (i:diskId) (state:State) (d:disk) : State :=
    match i with
    | d0 => Disks (Some d) (TD.disk1 state) proof
    | d1 => Disks (TD.disk0 state) (Some d) proof
    end.

  Inductive bg_step : State -> State -> Prop :=
  | step_id : forall state, bg_step state state
  | step_fail0 : forall d_0 d_1 pf,
      bg_step (Disks (Some d_0) (Some d_1) pf)
              (Disks None (Some d_1) proof)
  | step_fail1 : forall d_0 d_1 pf,
      bg_step (Disks (Some d_0) (Some d_1) pf)
              (Disks (Some d_0) None proof).

  Inductive op_step : forall `(op: Op T), Semantics State T :=
  | step_read : forall a i r state,
      match get_disk i state with
      | Some d => match d a with
                 | Some b0 => r = Working b0
                 | None => exists b, r = Working b
                 end
      | None => r = Failed
      end ->
      op_step (Read i a) state r state
  | step_write : forall a i b state r state',
      match get_disk i state with
      | Some d => state' = set_disk i state (diskUpd d a b) /\
                 r = Working tt
      | None => r = Failed /\ state' = state
      end ->
      op_step (Write i a b) state r state'
  | step_size : forall i state r,
      match get_disk i state with
      | Some d => r = Working (size d)
      | None => r = Failed
      end ->
      op_step (DiskSize i) state r state.

  Definition wipe (state:State) := state.

  Definition API : InterfaceAPI Op State :=
    background_step bg_step (@op_step) wipe.

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

End TD.
