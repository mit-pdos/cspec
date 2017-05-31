Require Import Automation.
Require Import Disk.AsyncDisk.

Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import TwoDisk.AsyncTwoDiskAPI.
Require Import SeqDisk.AsyncDiskAPI.

Require Import SeqDisk.AsyncReplicatedDisk.Step.
Require Import SeqDisk.AsyncReplicatedDisk.Init.
Require Import SeqDisk.AsyncReplicatedDisk.DiskSize.
Require Import SeqDisk.AsyncReplicatedDisk.Sync.
Require Import SeqDisk.AsyncReplicatedDisk.Recovery.
Require Import SeqDisk.AsyncReplicatedDisk.ReadWrite.

Require Import MaybeHolds.
Require Import Refinement.Interface.

(* The replicated disk implementation of the SeqDiskAPI (D.API) using two disks,
despite failures at the two disk level. *)

Module RD.

  Section ReplicatedDisk.

    (* The replicated disk implementation works for any implementation of two
    disks - [Interface] already captures the implementation and all the
    correctness proofs needed here. *)
    Variable (td:Interface TD.API).

    (* As the final step in giving the correctness of the replicated disk
    operations, we prove recovery specs that include the replicated disk Recover
    function. *)

    Ltac start := intros;
                  match goal with
                  | |- prog_spec _ _ (_ <- _; _) _ =>
                    eapply compose_recovery; eauto; simplify
                  end.

    (* it's sufficient to use regular hints to plug these specifications into
    the basic automation here *)
    Hint Resolve Read_ok Write_ok DiskSize_ok Recover_ok.

    Implicit Type (state:TD.State).

    (* TODO: clean up this proof *)
    Lemma histblock_histcrash_trans : forall h h' h'',
        histblock h (curr_val h') ->
        block_synced h' ->
        histcrash h' h'' ->
        histcrash h h''.
    Proof.
      unfold block_synced; intros.
      inversion H1; subst; clear H1.
      constructor.
      inversion H; subst; clear H.
      inversion H2; subst; clear H2.
      apply histblock_curr_eq; congruence.
      eapply H0 in H.
      apply histblock_curr_eq; congruence.
      inversion H2; subst; clear H2.
      econstructor; eauto.
      apply H0 in H; subst.
      econstructor; eauto.
    Qed.

    Lemma crashesTo_one_of_same : forall d hd hd',
        crashesTo hd d ->
        disk_synced hd ->
        crashesTo_one_of hd' hd' hd ->
        crashesTo hd' d.
    Proof.
      intros.
      destruct H, H0.
      inversion H1.
      eapply pointwise_rel_indomain; intros; try congruence.
      repeat match goal with
             | [ H: forall (_:addr), _  |- _ ] =>
               specialize (H a)
             end.
      destruct matches in *;
        intuition eauto using histblock_histcrash_trans.
    Qed.

    Hint Resolve crashesTo_one_of_same.

    Theorem Read_rok : forall a,
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
                   TD.disk0 state' |= crashesTo d /\
                   TD.disk1 state' |= crashesTo d;
             |})
          (Read td a) (_ <- irec td; Recover td)
          (refinement td).
    Proof.
      start.
      rename a0 into d.
      descend; (intuition eauto); simplify.
      descend; (intuition eauto); simplify.
      eapply pred_weaken; eauto.
      eapply pred_weaken; eauto.
    Qed.

    Lemma histblock_buffer : forall h b' b,
        histblock h b ->
        histblock (buffer b' h) b.
    Proof.
      intros.
      econstructor.
      autorewrite with block.
      inversion H; subst.
      econstructor.
      autorewrite with block; auto.
      constructor 2; auto.
    Qed.

    Hint Resolve histblock_buffer.

    Lemma crashesTo_upd_or_not : forall d a b d',
        crashesTo_one_of (diskUpdF d a (buffer b)) d d' ->
        crashesTo_one_of (diskUpdF d a (buffer b)) (diskUpdF d a (buffer b)) d'.
    Proof.
      intros.
      destruct H.
      econstructor; intros; try congruence.
      specialize (crashesTo_one_pointwise a0).
      is_eq a a0; autorewrite with upd in *.
      destruct matches in *; try contradiction.
      erewrite diskUpdF_eq in * by eauto.
      inversion Heqo; subst.
      intuition eauto.

      destruct matches in *.
    Qed.

    Hint Resolve crashesTo_upd_or_not.

    Theorem Write_rok : forall a b,
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
                   (TD.disk0 state' |= crashesTo d /\
                    TD.disk1 state' |= crashesTo d) \/
                   (TD.disk0 state' |= crashesTo (diskUpdF d a (buffer b)) /\
                    TD.disk1 state' |= crashesTo (diskUpdF d a (buffer b)));
             |})
          (Write td a b) (_ <- irec td; Recover td)
          (refinement td).
    Proof.
      start.
      rename a0 into d.
      descend; (intuition eauto); simplify.
      - descend; (intuition eauto); simplify.
        left.
        intuition eauto using pred_weaken.
      - descend; (intuition eauto); simplify.
        right.
        intuition eauto using pred_weaken.
      - descend; (intuition eauto); simplify.
        right.
        intuition eauto using pred_weaken.
    Qed.

  End ReplicatedDisk.

End RD.
