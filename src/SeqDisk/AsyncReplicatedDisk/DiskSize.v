Require Import Automation.
Require Import Disk.AsyncDisk.

Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import
        TwoDisk.AsyncTwoDiskAPI
        TwoDisk.AsyncTwoDiskTheorems
        TwoDisk.TwoDiskFacts.
Require Import SeqDisk.AsyncReplicatedDisk.Step.

Require Import MaybeHolds.

Section ReplicatedDisk.

  Variable (td:Interface TD.API).

  Definition DiskSize : prog nat :=
    msz <- Prim td (TD.DiskSize d0);
      match msz with
      | Working sz => Ret sz
      | Failed => msz <- Prim td (TD.DiskSize d1);
                   match msz with
                   | Working sz => Ret sz
                   | Failed => Ret 0
                   end
      end.

    Hint Resolve both_disks_not_missing : false.

    Hint Resolve then_wipe_missing.
    Hint Resolve pred_weaken.

    Theorem DiskSize_ok :
      prog_spec
        (fun '(d_0, d_1) state =>
           {|
             pre :=
               TD.disk0 state |= covered d_0 /\
               TD.disk1 state |= covered d_1 /\
               size d_0 = size d_1;
             post :=
               fun r state' =>
                 r = size d_0 /\
                 r = size d_1 /\
                 TD.disk0 state' |= covered d_0 /\
                 TD.disk1 state' |= covered d_1;
             recover :=
               fun _ state' =>
                 TD.disk0 state' |= crashesTo d_0 /\
                 TD.disk1 state' |= crashesTo d_1;
           |})
        (DiskSize)
        (irec td)
        (refinement td).
    Proof.
      unfold DiskSize.

      step.
      destruct r; step.
      destruct r; step.
    Qed.

End ReplicatedDisk.

Hint Resolve DiskSize_ok.
