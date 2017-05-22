Require Import Automation.
Require Import Disk.

Require Import Refinement.Interface.
Require Import TwoDisk.TwoDiskAPI TwoDisk.TwoDiskTheorems.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.

Require Import
        SeqDisk.ReplicatedDisk.Step
        SeqDisk.ReplicatedDisk.TwoDiskFacts.

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
  Theorem Read_ok : forall a,
      prog_rspec
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
    intros; eapply prog_rok_to_rspec; simplify.

    unfold Read.

    step.
    descend; intuition eauto.

    destruct r; step.
    descend; (intuition eauto); simplify.

    destruct r; step.
  Qed.

  Theorem Write_ok : forall a b,
      prog_rspec
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
    intros; eapply prog_rok_to_rspec; simplify.
    intuition eauto.

    unfold Write.

    step.
    descend; intuition eauto 10.
    destruct r; step.
    descend; intuition eauto.

    step.
    destruct r; (intuition eauto); simplify.
    destruct (lt_dec a (size a0)).
    eauto 10.
    autorewrite with upd in *; eauto.

    descend; (intuition eauto); simplify; eauto 10.
    destruct r; step.
  Qed.

End ReplicatedDiskReadWrite.
