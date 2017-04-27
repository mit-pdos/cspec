Require Import Prog.
Require Import Disk.

Inductive diskId := d0 | d1.

Module TD.

  Inductive Op : Type -> Type :=
  | Read (i:diskId) (a:addr) : Op block
  | Write (i:diskId) (a:addr) (b:block) : Op unit.

  Definition prog := Prog.prog Op.

  (** The state the program manipulates as it executes. *)
  Record State :=
    Disks { disk0 : disk;
            disk1 : disk; }.

  (** Get a particular disk from a state by id. *)
  Definition get_disk (i:diskId) (state:State) : disk :=
    match i with
    | d0 => disk0 state
    | d1 => disk1 state
    end.

  (** Apply an update function [up] to the disk identified by [i] in the state
      [state]. *)
  Definition upd_disk (i:diskId) (state:State) (up:disk -> disk) : State :=
    match i with
    | d0 => let 'Disks d_0 d_1 := state in Disks (up d_0) d_1
    | d1 => let 'Disks d_0 d_1 := state in Disks d_0 (up d_1)
    end.

  Inductive step : Semantics Op State :=
  | step_read : forall a i b state,
      match get_disk i state a with
      | Some b0 => b = b0
      | None => True
      end ->
      step (Read i a) state b state
  | step_write : forall a i b state,
      let up := match get_disk i state a with
                | Some _ => fun d => upd d a b
                | None => fun d => d
                end in
      step (Write i a b) state tt (upd_disk i state up).

  Definition exec := Prog.exec step.
  Definition exec_recover := Prog.exec_recover step.

End TD.
