Require Export Disk.
Require Import Implements.

Inductive diskId := d0 | d1.

(* TDSpec is an API for operations that manipulate two disks. *)
Module TDSpec.

  Record State :=
    Disks { disk0: disk;
            disk1: disk; }.

  Definition get_disk (id:diskId) (state:State) : disk :=
    match id with
    | d0 => disk0 state
    | d1 => disk1 state
    end.

  Definition upd_disk (i:diskId) (f: disk -> disk) (state:State) : State :=
    let 'Disks d_0 d_1 := state in
    match i with
    | d0 => Disks (f d_0) d_1
    | d1 => Disks d_0 (f d_1)
    end.

  Lemma get_disk1_upd_d0 : forall state f,
      disk1 (upd_disk d0 f state) = disk1 state.
  Proof.
    destruct state; eauto.
  Qed.

  Definition Read i a : Semantics block :=
    StepRel (fun state r state' =>
               match get_disk i state a with
               | Some v0 => r = v0
               | None => True
               end /\ state' = state).

  Definition Write i a b : Semantics unit :=
    StepRel (fun state r state' =>
               match get_disk i state a with
               | Some v0 => state' = upd_disk i (fun d => upd d a b) state
               | None => state' = state (* silently fails *)
               end).

End TDSpec.
