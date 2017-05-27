Require Import Automation.
Require Import Disk.SimpleDisk.

Require Import Refinement.Interface.
Require Import
        TwoDisk.TwoDiskAPI
        TwoDisk.TwoDiskTheorems
        TwoDisk.TwoDiskFacts.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.

Require Import SeqDisk.ReplicatedDisk.Step.

Require Import MaybeHolds.

Section ReplicatedDiskReadWrite.

  Variable (td:Interface TD.API).

  Definition Read (a:addr) : prog block :=
    mv0 <- Prim td (TD.Read d0 a);
      match mv0 with
      | Working v => Ret v
      | Failed => mv2 <- Prim td (TD.Read d1 a);
                   match mv2 with
                   | Working v => Ret v
                   | Failed => Ret block0
                   end
      end.

  Definition Write (a:addr) (b:block) : prog unit :=
    _ <- Prim td (TD.Write d0 a b);
      _ <- Prim td (TD.Write d1 a b);
      Ret tt.

  Hint Resolve pred_missing.
  Hint Resolve both_disks_not_missing : false.

  Implicit Type (state:TD.State).

  Theorem Read_ok : forall a,
      prog_spec
        (fun d state =>
           {|
             pre := TD.disk0 state |= eq d /\
                    TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                 d a |= eq r /\
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
             recover :=
               fun _ state' =>
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
           |})
        (Read a)
        (irec td)
        (refinement td).
  Proof.
    unfold Read.

    step.

    destruct r; step.
    destruct r; step.
  Qed.

  Theorem Write_ok : forall a b,
      prog_spec
        (fun d state =>
           {|
             pre :=
               TD.disk0 state |= eq d /\
               TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                 r = tt /\
                 TD.disk0 state' |= eq (diskUpd d a b) /\
                 TD.disk1 state' |= eq (diskUpd d a b);
             recover :=
               fun _ state' =>
                 (TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d) \/
                 (a < size d /\
                  TD.disk0 state' |= eq (diskUpd d a b) /\
                  TD.disk1 state' |= eq d) \/
                 (TD.disk0 state' |= eq (diskUpd d a b) /\
                  TD.disk1 state' |= eq (diskUpd d a b));
           |})
        (Write a b)
        (irec td)
        (refinement td).
  Proof.
    unfold Write.

    step.
    destruct r; step.
    descend; intuition eauto.

    step.
    destruct r; (intuition eauto); simplify.
    destruct (lt_dec a (size a')).
    eauto 10.
    autorewrite with upd in *; eauto.

    destruct r; step.
  Qed.

End ReplicatedDiskReadWrite.
