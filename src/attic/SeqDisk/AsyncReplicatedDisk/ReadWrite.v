Require Import Automation.
Require Import Disk.AsyncDisk.

Require Import Refinement.Interface.
Require Import
        TwoDisk.AsyncTwoDiskAPI
        TwoDisk.AsyncTwoDiskTheorems
        TwoDisk.TwoDiskFacts.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.

Require Import SeqDisk.AsyncReplicatedDisk.Step.

Require Import MaybeHolds.

Section AsyncReplicatedDisk.

  Variable (td:Interface TD.API).

  Definition Read (a:addr) : proc block :=
    mv0 <- Prim td (TD.Read d0 a);
      match mv0 with
      | Working v => Ret v
      | Failed => mv2 <- Prim td (TD.Read d1 a);
                   match mv2 with
                   | Working v => Ret v
                   | Failed => Ret block0
                   end
      end.

  Definition Write (a:addr) (b:block) : proc unit :=
    _ <- Prim td (TD.Write d0 a b);
      _ <- Prim td (TD.Write d1 a b);
      Ret tt.

  Hint Resolve pred_missing.
  Hint Resolve both_disks_not_missing : false.

  Implicit Type (state:TD.State).

  Hint Resolve then_wipe_missing.
  Hint Resolve pred_weaken.

  Theorem Read_ok : forall a,
      proc_spec
        (fun d state =>
           {|
             pre := TD.disk0 state |= covered d /\
                    TD.disk1 state |= covered d;
             post :=
               fun r state' =>
                 d a |= curr_val_eq r /\
                 TD.disk0 state' |= covered d /\
                 TD.disk1 state' |= covered d;
             recover :=
               fun _ state' =>
                 TD.disk0 state' |= crashesTo d /\
                 TD.disk1 state' |= crashesTo d;
           |})
        (Read a)
        (irec td)
        (interface_abs td).
  Proof.
    unfold Read.

    step.

    destruct r; step.
    destruct r; step.
  Qed.

  Theorem Write_ok : forall a b,
      proc_spec
        (fun d state =>
           {|
             pre :=
               TD.disk0 state |= covered d /\
               TD.disk1 state |= covered d;
             post :=
               fun r state' =>
                 r = tt /\
                 TD.disk0 state' |= covered (diskUpdF d a (buffer b)) /\
                 TD.disk1 state' |= covered (diskUpdF d a (buffer b));
             recover :=
               fun _ state' =>
                 (TD.disk0 state' |= crashesTo d /\
                  TD.disk1 state' |= crashesTo d) \/
                 (a < size d /\
                  TD.disk0 state' |= crashesTo (diskUpdF d a (buffer b)) /\
                  TD.disk1 state' |= crashesTo d) \/
                 (TD.disk0 state' |= crashesTo (diskUpdF d a (buffer b)) /\
                  TD.disk1 state' |= crashesTo (diskUpdF d a (buffer b)));
           |})
        (Write a b)
        (irec td)
        (interface_abs td).
  Proof.
    unfold Write.

    step.
    destruct r; step.
    descend; intuition eauto.

    step.
    destruct r; (intuition eauto); simplify.
    destruct (lt_dec a (size a')).
    right; left; intuition eauto.
    autorewrite with upd in *; eauto.
    destruct r; step.
  Qed.

End AsyncReplicatedDisk.
