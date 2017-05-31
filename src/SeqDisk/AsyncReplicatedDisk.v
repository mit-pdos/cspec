Require Import Automation.
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

    Theorem DiskSize_rok :
      prog_spec
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
                 TD.disk0 state' |= crashesTo d /\
                 TD.disk1 state' |= crashesTo d;
           |})
        (DiskSize td) (_ <- irec td; Recover td)
        (refinement td).
    Proof.
      start.

      rename a into d.
      descend; (intuition eauto); simplify.
      descend; (intuition eauto); simplify.
      eapply pred_weaken; eauto.
      eapply pred_weaken; eauto.
    Qed.

    Theorem Sync_rok :
      prog_spec
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
                 TD.disk0 state' |= crashesTo d /\
                 TD.disk1 state' |= crashesTo d;
           |})
        (Sync td) (_ <- irec td; Recover td)
        (refinement td).
    Proof.
      start.

      rename a into d.
      descend; (intuition eauto); simplify.
      - descend; (intuition eauto); simplify.
        eauto using pred_weaken.
        eauto using pred_weaken.
      - descend; (intuition eauto); simplify.
        all: admit. (* need to show crashesTo is weaker than then_flush
        (flushing is one possible crash state, so this should be true) *)
      - descend; (intuition eauto); simplify.
        all: admit.
    Admitted.

    (* Now we gather up the implementation and all the correctness proofs,
    expressing them in terms of the high-level API in D.API. *)

    (* First, we prove some lemmas that re-express the D.API semantics in more
    convenient terms (in some cases, just for the sake of the automation). *)

    Lemma read_step : forall a (state state':D.State) b,
        state a |= (fun bs => curr_val bs = b) ->
        state' = state ->
        D.step (D.Read a) state b state'.
    Proof.
      intros; subst.
      constructor; auto.
      intros.
      replace (state a) in *; auto.
    Qed.

    Lemma write_step : forall a b (state state':D.State) u,
        state' = diskUpdF state a (buffer b) ->
        D.step (D.Write a b) state u state'.
    Proof.
      intros; subst.
      destruct u.
      econstructor; eauto.
    Qed.

    Lemma sync_step : forall (state state':D.State) u,
        state' = flush state ->
        D.step (D.Sync) state u state'.
    Proof.
      intros; subst.
      destruct u.
      econstructor; eauto.
    Qed.

    Lemma disk_size_step : forall (state state':D.State) r,
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

    (* TODO: fix [D.State] to allow two durable values *)
    Definition rd_abstraction (state:TD.State) : D.State :=
      match state with
      | TD.Disks (Some d) _ _ => d
      | TD.Disks None (Some d) _ => d
      | _ => empty_disk (* impossible *)
      end.

    Definition rd_invariant (state:TD.State) :=
      match state with
      | TD.Disks (Some d_0) (Some d_1) _ =>
        d_0 = d_1
      | _ => True
      end.

    (* Finally, we put together the pieces of the [Interface]. Here we also
    convert from our specificatiosn above to the exact form that an Interface
    uses; the proofs are automatic after defining the lemmas above about D.step
    and the layer refinement. *)

    Definition d_op_impl T (op:D.Op T) : prog T :=
      match op with
      | D.Read a => Read td a
      | D.Write a b => Write td a b
      | D.Sync => Sync td
      | D.DiskSize => DiskSize td
      end.

    Definition rd_refinement :=
      refinement_compose
        (refinement td)
        {| invariant := rd_invariant;
           abstraction := rd_abstraction; |}.

    Definition impl : InterfaceImpl D.Op :=
      {| op_impl := d_op_impl;
         recover_impl := _ <- irec td; Recover td;
         init_impl := then_init (iInit td) (Init td) |}.

    Hint Resolve Read_rok Write_rok Sync_rok DiskSize_rok Recover_rok.

    Theorem state_some_disks : forall state,
        exists d_0 d_1,
          TD.disk0 state |= eq d_0 /\
          TD.disk1 state |= eq d_1.
    Proof.
      destruct state.
      destruct disk0, disk1; simpl; eauto.
      exfalso; eauto.
    Qed.

    Theorem rd_crash_effect_valid :
      crash_effect_valid {| invariant := rd_invariant;
                            abstraction := rd_abstraction |}
                         TD.wipe D.wipe.
    Proof.
      econstructor; intros; simpl.
      - unfold rd_abstraction.
        destruct w; simpl.
        destruct disk0, disk1; auto.
        exfalso; eauto.
      - eapply diskMem_ext_eq.
        extensionality a.
        simpl.
        destruct matches.
    Qed.

    Definition rd : Interface D.API.
      unshelve econstructor.
      - exact impl.
      - exact rd_refinement.
      - intros.
        destruct op; unfold op_spec;
          apply spec_refinement_compose;
          eapply prog_spec_weaken; eauto;
            unfold spec_impl; simplify.
        + exists (mapDisk (rd_abstraction state)
                     (fun bs => {| current_val := curr_val bs;
                                durable_vals := durable_val bs::nil; |})).
          (intuition eauto); simplify.
          all: admit.
        + all: admit.
        + all: admit.
        + all: admit.
      - eapply rec_noop_compose; eauto; simpl.
        apply rd_crash_effect_valid.
        eapply prog_spec_weaken; eauto;
          unfold spec_impl; simplify.
        unfold crash_invariant in *; simpl in *; repeat deex.
        admit.
      - eapply then_init_compose; eauto.
        eapply prog_spec_weaken; unfold spec_impl; simplify.
        admit.
      - eapply crash_effect_compose; unfold wipe_valid;
          eauto using crash_effect_ok; simpl; intros.
        apply rd_crash_effect_valid.
        apply rd_crash_effect_valid.
    Admitted.

  End ReplicatedDisk.

End RD.
