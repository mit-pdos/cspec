Require Import Prog.
Require Import Disk.

Inductive diskId := d0 | d1.

Inductive DiskResult T :=
| Working (v:T)
| Failed.

Arguments Failed {T}.

Module TD.


  Inductive Op : Type -> Type :=
  | Read (i:diskId) (a:addr) : Op (DiskResult block)
  | Write (i:diskId) (a:addr) (b:block) : Op (DiskResult unit).

  Definition prog := Prog.prog Op.

  (** The state the program manipulates as it executes. *)
  Record State :=
    Disks { disk0 : option disk;
            disk1 : option disk;
            some_disk_works : exists d, disk0 = Some d \/ disk1 = Some d }.

  Arguments Disks disk0 disk1 some_disk_works : clear implicits.

  (** Get a particular disk from a state by id. *)
  Definition get_disk (i:diskId) (state:State) : option disk :=
    match i with
    | d0 => disk0 state
    | d1 => disk1 state
    end.

  Definition set_disk (i:diskId) (state:State) (d:disk) : State :=
    match i with
    | d0 => let 'Disks _ d_1 _ := state in Disks (Some d) d_1 ltac:(eauto)
    | d1 => let 'Disks d_0 _ _ := state in Disks d_0 (Some d) ltac:(eauto)
    end.

  Inductive bg_step : State -> State -> Prop :=
  | step_id : forall state, bg_step state state
  | step_fail0 : forall d_0 d_1 pf,
      bg_step (Disks (Some d_0) (Some d_1) pf)
              (Disks None (Some d_1) ltac:(eauto))
  | step_fail1 : forall d_0 d_1 pf,
      bg_step (Disks (Some d_0) (Some d_1) pf)
              (Disks (Some d_0) None ltac:(eauto)).

  Inductive op_step : Semantics Op State :=
  | step_read : forall a i r state,
      match get_disk i state with
      | Some d => match d a with
                 | Some b0 => r = Working b0
                 | None => exists b, r = Working b
                 end
      | None => r = Failed
      end ->
      op_step (Read i a) state r state
  | step_write : forall a i b state,
      let r := if get_disk i state then Working tt else Failed in
      let state' := match get_disk i state with
                | Some d => match d a with
                           | Some _ => set_disk i state (upd d a b)
                           | None => state (* oob writes silently fail *)
                           end
                | None => state
                end in
      op_step (Write i a b) state r state'.

  Definition step := background_step bg_step op_step.

  Definition exec := Prog.exec step.
  Definition exec_recover := Prog.exec_recover step.

End TD.
