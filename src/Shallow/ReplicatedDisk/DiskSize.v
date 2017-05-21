Require Import Automation.
Require Import Disk.

Require Import Shallow.Interface.
Require Import Shallow.TwoDiskAPI Shallow.TwoDiskProgTheorems.
Require Import Shallow.ProgLang.Prog.
Require Import Shallow.ProgLang.Hoare.
Require Import Shallow.ReplicatedDisk.Step.
Require Import Shallow.ReplicatedDisk.TwoDiskFacts.

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

    Inductive DiskStatus :=
    | FullySynced
    | OutOfSync (a:addr) (b:block).

    Hint Resolve both_disks_not_missing : false.

    Hint Rewrite diskUpd_size : rd.

    (* TODO: why does this not have a simpler spec? *)
    Theorem DiskSize_ok :
      prog_rok
        (fun '(d, s) state =>
           {|
             pre :=
               match s with
               | FullySynced => TD.disk0 state |= eq d /\
                               TD.disk1 state |= eq d
               | OutOfSync a b => a < size d /\
                                 TD.disk0 state |= eq (diskUpd d a b) /\
                                 TD.disk1 state |= eq d
               end;
             post :=
               fun r state' =>
                 r = size d /\
                 match s with
                 | FullySynced => TD.disk0 state' |= eq d /\
                                 TD.disk1 state' |= eq d
                 | OutOfSync a b => a < size d /\
                                   TD.disk0 state' |= eq (diskUpd d a b) /\
                                   TD.disk1 state' |= eq d
                 end;
             recover :=
               fun _ state' =>
                 match s with
                 | FullySynced => TD.disk0 state' |= eq d /\
                                 TD.disk1 state' |= eq d
                 | OutOfSync a b => a < size d /\
                                   TD.disk0 state' |= eq (diskUpd d a b) /\
                                   TD.disk1 state' |= eq d
                 end;
           |})
        (DiskSize)
        (irec td)
        (refinement td).
    Proof.
      unfold DiskSize.

      step.
      destruct s; descend; intuition eauto.
      - destruct r; step.
        descend; intuition eauto.

        destruct r; step.
      - destruct r; step.
        descend; intuition eauto.

        destruct r; step.
    Qed.

End ReplicatedDisk.

Hint Extern 1 {{ DiskSize _; _ }} => apply DiskSize_ok : prog.
