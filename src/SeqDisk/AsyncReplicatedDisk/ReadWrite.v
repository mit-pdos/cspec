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

  Lemma then_wipe_missing : forall md,
      md |= then_wipe missing ->
      md |= missing.
  Proof.
    unfold then_wipe, missing; intros.
    destruct md; simpl in *; repeat deex; eauto.
  Qed.

  Hint Resolve then_wipe_missing.

  Theorem Read_ok : forall a,
      prog_spec
        (fun d state =>
           {|
             pre := TD.disk0 state |= covered d /\
                    TD.disk1 state |= covered d;
             post :=
               fun r state' =>
                 d a |= (fun bs => curr_val bs = r) /\
                 TD.disk0 state' |= covered d /\
                 TD.disk1 state' |= covered d;
             recover :=
               fun _ state' =>
                 TD.disk0 state' |= then_wipe (covered d) /\
                 TD.disk1 state' |= then_wipe (covered d);
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
               TD.disk0 state |= covered d /\
               TD.disk1 state |= covered d;
             post :=
               fun r state' =>
                 r = tt /\
                 TD.disk0 state' |= covered (diskUpdF d a (buffer b)) /\
                 TD.disk1 state' |= covered (diskUpdF d a (buffer b));
             recover :=
               fun _ state' =>
                 (TD.disk0 state' |= then_wipe (covered d) /\
                  TD.disk1 state' |= then_wipe (covered d)) \/
                 (a < size d /\
                  TD.disk0 state' |= then_wipe (covered (diskUpdF d a (buffer b))) /\
                  TD.disk1 state' |= then_wipe (covered d)) \/
                 (TD.disk0 state' |= then_wipe (covered (diskUpdF d a (buffer b))) /\
                  TD.disk1 state' |= then_wipe (covered (diskUpdF d a (buffer b))));
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

End AsyncReplicatedDisk.
