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

  Definition Sync : proc unit :=
    _ <- Prim td (TD.Sync d0);
      _ <- Prim td (TD.Sync d1);
      Ret tt.

  Theorem disk0_wipe_flush_stable : forall state state' d,
      TD.disk0 state |= then_flush (covered d) ->
      TD.wipe state state' ->
      TD.disk0 state' |= then_flush (covered d).
  Proof.
    unfold TD.wipe; intros; subst.
    destruct state; simpl in *.
    destruct disk0, disk1; simpl in *;
      autorewrite with flush; eauto.
  Qed.

  Theorem disk1_wipe_flush_stable : forall state state' d,
      TD.disk1 state |= then_flush (covered d) ->
      TD.wipe state state' ->
      TD.disk1 state' |= then_flush (covered d).
  Proof.
    unfold TD.wipe; intros; subst.
    destruct state; simpl in *.
    destruct disk0, disk1; simpl in *;
      autorewrite with flush; eauto.
  Qed.

  Hint Resolve disk0_wipe_flush_stable disk1_wipe_flush_stable.

  Hint Resolve pred_weaken.

  Theorem Sync_ok :
    proc_spec
      (fun '(d_0, d_1) state =>
         {|
           pre :=
             TD.disk0 state |= covered d_0 /\
             TD.disk1 state |= covered d_1;
           post :=
             fun r state' =>
               r = tt /\
               TD.disk0 state' |= then_flush (covered d_0) /\
               TD.disk1 state' |= then_flush (covered d_1);
           recover :=
             fun _ state' =>
               (TD.disk0 state' |= crashesTo d_0 /\
                TD.disk1 state' |= crashesTo d_1) \/
               (TD.disk0 state' |= then_flush (covered d_0) /\
                TD.disk1 state' |= crashesTo d_1) \/
               (TD.disk0 state' |= then_flush (covered d_0) /\
                TD.disk1 state' |= then_flush (covered d_1));
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
