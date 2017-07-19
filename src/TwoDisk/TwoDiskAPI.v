Require Import POCS.

Set Implicit Arguments.

Inductive diskId := d0 | d1.

Inductive DiskResult T :=
| Working (v:T)
| Failed.

Arguments Failed {T}.


Module TD.

  (** The state the program manipulates as it executes. *)
  Record StateR diskT :=
    Disks { disk0 : option diskT;
            disk1 : option diskT;
            some_disk_works : disk0 = None -> disk1 = None -> False }.

  Arguments Disks {diskT} disk0 disk1 some_disk_works.

  Inductive Op : Type -> Type :=
  | Read (i:diskId) (a:addr) : Op (DiskResult block)
  | Write (i:diskId) (a:addr) (b:block) : Op (DiskResult unit)
  (* get disk size in blocks *)
  | DiskSize (i:diskId) : Op (DiskResult nat).

  (** Get a particular disk from a state by id. *)
  Definition get_disk {diskT} (i:diskId) (state:StateR diskT) : option diskT :=
    match i with
    | d0 => disk0 state
    | d1 => disk1 state
    end.

  Local Lemma d0_is_some {diskT} (d_0: diskT) (d_1: option diskT) :
    Some d_0 = None -> d_1 = None -> False.
  Proof.
    congruence.
  Qed.

  Local Lemma d1_is_some {diskT} (d_0: option diskT) (d_1: diskT) :
    d_0 = None -> Some d_1 = None -> False.
  Proof.
    congruence.
  Qed.

  Local Notation proof := (ltac:(first [ apply d0_is_some | apply d1_is_some ])) (only parsing).

  Definition set_disk {diskT} (i:diskId) (state:StateR diskT) (d:diskT) : StateR diskT :=
    match i with
    | d0 => Disks (Some d) (disk1 state) proof
    | d1 => Disks (disk0 state) (Some d) proof
    end.

  (* shadow state with a specialized version for sequential disks *)
  Definition State := StateR disk.

  (* help out type inference *)
  Implicit Type (state:State).

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

  Definition wipe state state' := state' = state.
  Definition inited state := True.

  Inductive bg_failure {diskT} : StateR diskT -> StateR diskT -> Prop :=
  | step_id : forall (state: StateR diskT), bg_failure state state
  | step_fail0 : forall d_0 d_1 pf,
      bg_failure (Disks (Some d_0) (Some d_1) pf)
                 (Disks None (Some d_1) proof)
  | step_fail1 : forall d_0 d_1 pf,
      bg_failure (Disks (Some d_0) (Some d_1) pf)
                 (Disks (Some d_0) None proof).

  Definition API : InterfaceAPI Op State :=
    {|
      op_sem := pre_step bg_failure (@op_step);
      crash_effect := wipe;
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
    | [ H: bg_failure _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

End TD.
