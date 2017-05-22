Require Import Automation.
Require Import Disk.

Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import TwoDisk.TwoDiskAPI.
Require Import TwoDisk.TwoDiskTheorems.
Require Import
        SeqDisk.ReplicatedDisk.Step
        SeqDisk.ReplicatedDisk.TwoDiskFacts.

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

    Theorem DiskSize_ok :
      prog_ok
        (fun '(d_0, d_1) state =>
           {|
             pre :=
               TD.disk0 state |= eq d_0 /\
               TD.disk1 state |= eq d_1 /\
               size d_0 = size d_1;
             post :=
               fun r state' =>
                 r = size d_0 /\
                 r = size d_1 /\
                 TD.disk0 state' |= eq d_0 /\
                 TD.disk1 state' |= eq d_1;
             recover :=
               fun _ state' =>
                 TD.disk0 state' |= eq d_0 /\
                 TD.disk1 state' |= eq d_1;
           |})
        (DiskSize)
        (irec td)
        (refinement td).
    Proof.
      unfold DiskSize.

      step.
      descend; intuition eauto.

      destruct r; step.
      descend; intuition eauto.

      destruct r; step.
    Qed.

End ReplicatedDisk.

Hint Extern 1 {{ DiskSize _; _ }} => apply DiskSize_ok : prog.
