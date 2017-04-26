Require Import Disk.
Require Import Mem.
Require Import Implements.

Inductive diskId := d0 | d1.

(* TD is an API for operations that manipulate two disks. *)
Module TD.

  Axiom Read : diskId -> addr -> IO block.
  Axiom Write : diskId -> addr -> block -> IO unit.

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

  Axiom abstraction : world -> State.

  Axiom Read_spec : forall i a,
      implements
        (StepRel (fun state v state' =>
                    match get_disk i state a with
                    | Some v0 => v = v0
                    | None => True
                    end /\ state' = state))
        (io_semantics (Read i a))
        abstraction.

  Axiom Write_spec : forall i a b,
      implements
        (StepRel (fun state v state' =>
                    match get_disk i state a with
                    | Some v0 => state' = upd_disk i (fun d => upd d a b) state
                    | None => True (* new disk is arbitrary *)
                    end))
        (io_semantics (Write i a b))
        abstraction.

End TD.

(* Local Variables: *)
(* company-coq-local-symbols: (("State" . ?Σ) ("state" . ?σ) ("state'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
