Require Import Automation.
Require Import Disk.SimpleDisk.

Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import
        TwoDisk.TwoDiskAPI
        TwoDisk.TwoDiskTheorems
        TwoDisk.TwoDiskFacts.
Require Import SeqDisk.ReplicatedDisk.Step.

Require Import MaybeHolds.

Section ReplicatedDisk.

  Variable (td:Interface TD.API).

  Definition Sync : prog unit :=
    _ <- Prim td (TD.Sync d0);
      _ <- Prim td (TD.Sync d1);
      Ret tt.

  Hint Unfold TD.wipe : rd.

  Theorem Sync_ok :
    prog_spec
      (fun '(d_0, d_1) state =>
         {|
           pre :=
             TD.disk0 state |= eq d_0 /\
             TD.disk1 state |= eq d_1;
           post :=
             fun r state' =>
               r = tt /\
               TD.disk0 state' |= eq d_0 /\
               TD.disk1 state' |= eq d_1;
           recover :=
             fun _ state' =>
               TD.disk0 state' |= eq d_0 /\
               TD.disk1 state' |= eq d_1;
         |})
      (Sync)
      (irec td)
      (interface_abs td).
  Proof.
    unfold Sync.

    step.
    step.
    step.
  Qed.

End ReplicatedDisk.

Hint Resolve Sync_ok.
