Require Import Automation.
Require Import Pocs.Ensemble.
Require Import Disk.AsyncDisk.

Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import
        TwoDisk.AsyncTwoDiskAPI
        TwoDisk.AsyncTwoDiskTheorems.
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
                  | |- proc_spec _ _ (_ <- _; _) _ =>
                    eapply compose_recovery; eauto; simplify
                  end.

    (* it's sufficient to use regular hints to plug these specifications into
    the basic automation here *)
    Hint Resolve Read_ok Write_ok DiskSize_ok Recover_ok.

    Implicit Type (state:TD.State).

    Theorem histblock_histcrash_trans : forall h h' h'',
        In (curr_val h') (durable_vals h) ->
        hist_flushed h' ->
        histcrash h' h'' ->
        histcrash h h''.
    Proof.
      unfold hist_flushed; intros.
      inversion H1; subst; clear H1.
      rewrite H0 in *.
      inversion H2; subst; clear H2.
      econstructor; eauto.
    Qed.

    Theorem crashesTo_one_of_same : forall d hd hd',
        crashesTo hd d ->
        histdisk_flushed hd ->
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
      repeat simpl_match.
      destruct matches in *;
        intuition eauto using histblock_histcrash_trans.
    Qed.

    Hint Resolve crashesTo_one_of_same.

    Theorem crashesTo_one_of_same_wipeHist : forall hd hd',
        crashesTo_one_of hd' hd' hd ->
        histdisk_flushed hd ->
        wipeHist hd' hd.
    Proof.
      intros.
      destruct H, H0.
      eapply pointwise_rel_indomain; intros; try congruence.
      repeat match goal with
             | [ H: forall (_:addr), _  |- _ ] =>
               specialize (H a)
             end.
      repeat simpl_match.
      eapply wipeBlockhist_eq; eauto.
      intuition.
    Qed.

    Hint Resolve crashesTo_one_of_same_wipeHist.

    Theorem Read_rok : forall a,
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
                   exists d',
                     TD.disk0 state' |= crashesTo d' /\
                     TD.disk1 state' |= crashesTo d' /\
                     wipeHist d d';
             |})
          (Read td a) (_ <- irec td; Recover td)
          (interface_abs td).
    Proof.
      start.
      rename a0 into d.
      descend; (intuition eauto); simplify.
      descend; (intuition eauto); simplify.
      descend; intuition eauto.
    Qed.

    Theorem histblock_buffer : forall h b' b,
        In b (durable_vals h) ->
        In b (durable_vals (buffer b' h)).
    Proof.
      intros.
      autorewrite with block.
      eauto.
    Qed.

    Hint Resolve histblock_buffer.

    Theorem crashesTo_upd_or_not : forall d a b d',
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
                   exists d',
                   TD.disk0 state' |= crashesTo d' /\
                   TD.disk1 state' |= crashesTo d' /\
                   (wipeHist d d' \/
                    wipeHist (diskUpdF d a (buffer b)) d');
             |})
          (Write td a b) (_ <- irec td; Recover td)
          (interface_abs td).
    Proof.
      start.
      rename a0 into d.
      descend; (intuition eauto); simplify.
      - descend; (intuition eauto); simplify; finish.
      - descend; (intuition eauto); simplify; finish.
        autorewrite with upd; eauto.
      - descend; (intuition eauto); simplify; finish.
    Qed.

    Theorem DiskSize_rok :
      proc_spec
        (fun d state =>
           {|
             pre := TD.disk0 state |= covered d /\
                    TD.disk1 state |= covered d;
             post :=
               fun r state' =>
                 r = size d /\
                 TD.disk0 state' |= covered d /\
                 TD.disk1 state' |= covered d;
             recover :=
               fun _ state' =>
                 exists d',
                   TD.disk0 state' |= crashesTo d' /\
                   TD.disk1 state' |= crashesTo d' /\
                   wipeHist d d';
           |})
        (DiskSize td) (_ <- irec td; Recover td)
        (interface_abs td).
    Proof.
      start.

      rename a into d.
      descend; (intuition eauto); simplify; finish.
      descend; (intuition eauto); simplify; finish.
    Qed.

    (* TODO: simplify this proof *)
    Theorem then_flush_crashesTo : forall d d',
        then_flush (covered d) d' ->
        crashesTo d d'.
    Proof.
      unfold then_flush; intros; repeat deex.
      autounfold with disk in *; pointwise.
      apply collapse_current in H.
      apply curr_val_some_cache in Heqo1.
      econstructor; eauto.
      subst.
      rewrite <- H.
      eapply durable_includes_current.
      destruct b0; simpl in *; subst.
      econstructor; eauto.
      apply collapse_current in H; autorewrite with block in *; simpl in *.
      subst.
      eapply durable_includes_current.
    Qed.

    Hint Resolve then_flush_crashesTo.

    Theorem Sync_rok :
      proc_spec
        (fun d state =>
           {|
             pre := TD.disk0 state |= covered d /\
                    TD.disk1 state |= covered d;
             post :=
               fun r state' =>
                 r = tt /\
                 TD.disk0 state' |= then_flush (covered d) /\
                 TD.disk1 state' |= then_flush (covered d);
             recover :=
               fun _ state' =>
                 exists d',
                 TD.disk0 state' |= crashesTo d' /\
                 TD.disk1 state' |= crashesTo d' /\
                 wipeHist d d';
           |})
        (Sync td) (_ <- irec td; Recover td)
        (interface_abs td).
    Proof.
      start.

      rename a into d.
      descend; (intuition eauto); simplify.
      - descend; (intuition eauto); simplify; finish.
      - descend; (intuition eauto); simplify; finish.
        eauto using pred_weaken.
      - descend; (intuition eauto); simplify; finish.
        eauto using pred_weaken.
        eauto using pred_weaken.
    Qed.

    (* Now we gather up the implementation and all the correctness proofs,
    expressing them in terms of the high-level API in D.API. *)

    (* First, we prove some lemmas that re-express the D.API semantics in more
    convenient terms (in some cases, just for the sake of the automation). *)

    Theorem read_step : forall a (state state':D.State) b,
        state a |= curr_val_eq b ->
        state' = state ->
        D.step (D.Read a) state b state'.
    Proof.
      intros; subst.
      constructor; auto.
      intros.
      replace (state a) in *; auto.
    Qed.

    Theorem write_step : forall a b (state state':D.State) u,
        state' = diskUpdF state a (buffer b) ->
        D.step (D.Write a b) state u state'.
    Proof.
      intros; subst.
      destruct u.
      econstructor; eauto.
    Qed.

    Theorem sync_step : forall (state state':D.State) u,
        state' = flush state ->
        D.step (D.Sync) state u state'.
    Proof.
      intros; subst.
      destruct u.
      econstructor; eauto.
    Qed.

    Theorem disk_size_step : forall (state state':D.State) r,
        r = size state ->
        state' = state ->
        D.step (D.DiskSize) state r state'.
    Proof.
      intros; subst.
      econstructor; eauto.
    Qed.

    Hint Resolve read_step write_step sync_step disk_size_step.

    (* The proof will require a refinement; we build one up based on the
    two-disk state. *)

    Definition rd_layer_abstraction (state:TD.State) (d:D.State) :=
      TD.disk0 state |= covered d /\
      TD.disk1 state |= covered d.

    (* We re-express the abstraction and invariant's behavior in terms of the
       maybe holds (m |= F) statements in all of our specifications. *)

    Ltac crush :=
      intros; repeat match goal with
                     | [ state: TD.State |- _ ] => destruct state
                     | _ => deex
                     | _ => progress destruct matches in *
                     | _ => progress simpl in *
                     | _ => eauto
                     end.

    Definition state_hist (bs:blockstate) : blockhist :=
      {| current_val := curr_val bs;
         durable_vals := Add (curr_val bs)
                           (Singleton (durable_val bs));
         durable_includes_current := ltac:(auto); |}.

    Definition covering (d:disk) : histdisk :=
      mapDisk state_hist d.

    Theorem collapsesTo_state_hist : forall b,
        collapsesTo (state_hist b) b.
    Proof.
      unfold state_hist; destruct b; simpl; intros.
      econstructor; simpl; eauto.
    Qed.

    Theorem covered_covering : forall d,
        covered (covering d) d.
    Proof.
      intros.
      eapply pointwise_rel_indomain; intros; auto.
      simpl in *; repeat simpl_match.
      inversion H0; subst.
      eauto using collapsesTo_state_hist.
    Qed.

    Hint Resolve covered_covering.

    (* Finally, we put together the pieces of the [Interface]. *)

    Definition d_op_impl T (op:D.Op T) : proc T :=
      match op with
      | D.Read a => Read td a
      | D.Write a b => Write td a b
      | D.Sync => Sync td
      | D.DiskSize => DiskSize td
      end.

    Definition rd_abstraction :=
      abstraction_compose
        (interface_abs td)
        {| abstraction := rd_layer_abstraction; |}.

    Definition impl : InterfaceImpl D.Op :=
      {| op_impl := d_op_impl;
         recover_impl := _ <- irec td; Recover td;
         init_impl := then_init (iInit td) (Init td) |}.

    Hint Resolve Read_rok Write_rok Sync_rok DiskSize_rok Recover_rok.

    Theorem state_some_disks : forall state,
        exists d_0 d_1,
          TD.disk0 state |= covered d_0 /\
          TD.disk1 state |= covered d_1.
    Proof.
      destruct state.
      destruct disk0, disk1; simpl; eauto.
      exists (covering d), empty_disk; eauto.
      exists empty_disk, (covering d); eauto.
      solve_false.
    Qed.

    (* TODO: move up to AsyncDisk. Might be useful elsewhere, too. *)
    Theorem wipe_crashesTo : forall d d',
        covered d d' ->
        crashesTo d (wipeDisk d').
    Proof.
      autounfold with disk; intros.
      pointwise.
      unfold wipeBlockstate.
      econstructor; eauto.
      eapply collapse_durable; eauto.
    Qed.

    Theorem wipe_disk0_crashesTo : forall state d,
        TD.disk0 state |= covered d ->
        TD.disk0 (TD.disks_map wipeDisk state) |= crashesTo d.
    Proof.
      intros.
      destruct state.
      destruct disk0, disk1; simpl in *; eauto.

      eapply wipe_crashesTo; eauto.
      eapply wipe_crashesTo; eauto.
    Qed.

    Theorem wipe_disk1_crashesTo : forall state d,
        TD.disk1 state |= covered d ->
        TD.disk1 (TD.disks_map wipeDisk state) |= crashesTo d.
    Proof.
      intros.
      destruct state.
      destruct disk0, disk1; simpl in *; eauto.
      eapply wipe_crashesTo; eauto.
      eapply wipe_crashesTo; eauto.
    Qed.

    Hint Resolve wipe_disk0_crashesTo wipe_disk1_crashesTo.

    Theorem crashesTo_synced_covered : forall d d',
        crashesTo d d' ->
        histdisk_flushed d ->
        covered d d'.
    Proof.
      autounfold with disk; intros; pointwise.
      (* TODO: this should be part of pointwise *)
      apply pointwise_prop_holds with (a:=a) in H0;
        simpl_match.
      inversion H0.
      inversion H; subst; clear H.
      rewrite H2 in *.
      inversion H1; subst.
      econstructor; eauto.
      simpl.
      eapply durable_includes_current.
    Qed.

    Hint Resolve crashesTo_synced_covered.

    Theorem wipeBlock_hist_flushed : forall h h',
        wipeBlockhist h h' ->
        hist_flushed h'.
    Proof.
      destruct 1.
      econstructor; eauto.
    Qed.

    Hint Resolve wipeBlock_hist_flushed.

    Theorem wipeHist_flushed : forall d d',
        wipeHist d d' ->
        histdisk_flushed d'.
    Proof.
      intros.
      destruct H.
      econstructor; intros.
      specialize (pointwise_rel_holds a).
      destruct matches in *; try contradiction; eauto.
    Qed.

    Hint Resolve wipeHist_flushed.

    Hint Resolve then_flush_covered.

    Definition rd : Interface D.API.
      unshelve econstructor.
      - exact impl.
      - exact rd_abstraction.

      - intros.
        destruct op; unfold op_spec;
          apply spec_abstraction_compose;
          eapply proc_spec_weaken; eauto;
            unfold spec_impl, rd_layer_abstraction; simplify.
        + descend; (intuition eauto); simplify.
          descend; intuition eauto using pred_weaken.
        + descend; (intuition eauto); simplify.
          descend; intuition eauto using pred_weaken.
        + descend; (intuition eauto); simplify.
          descend; intuition eauto using pred_weaken.
          descend; intuition eauto using pred_weaken.
        + descend; (intuition eauto); simplify.
          descend; intuition eauto using pred_weaken.

      - eapply rec_noop_compose; eauto; simpl.
        unfold Recover_spec, rd_layer_abstraction; simplify.
        unfold TD.wipe in *; subst.
        exists state0', state0'.
        intuition eauto.
        repeat deex.
        unfold D.wipe.
        descend; intuition eauto.
        eapply pred_weaken; eauto.
        eapply pred_weaken; eauto.
      - eapply then_init_compose; eauto.
        eapply proc_spec_weaken; unfold spec_impl; simplify.
        pose proof (state_some_disks state); simplify.
        descend; intuition eauto.
        destruct v; simplify; finish.
        unfold rd_layer_abstraction; eauto.

        Grab Existential Variables.
        all: auto.
    Defined.

  End ReplicatedDisk.

End RD.
