Require Import POCS.

Require Import ReplicatedDisk.ReplicatedDiskAPI.
Require Import TwoDisk.TwoDiskAPI.

Module ReplicatedDisk.

  Section Implementation.

    Variable (td : Interface TD.API).

    Definition read (a:nat) : proc block :=
      mv0 <- Prim td (TD.Read d0 a);
      match mv0 with
      | Working v => Ret v
      | Failed =>
        mv2 <- Prim td (TD.Read d1 a);
        match mv2 with
        | Working v => Ret v
        | Failed => Ret block0
        end
      end.

    Definition write (a:nat) (b:block) : proc unit :=
      _ <- Prim td (TD.Write d0 a b);
      _ <- Prim td (TD.Write d1 a b);
      Ret tt.

    Definition diskSize : proc nat :=
      msz <- Prim td (TD.DiskSize d0);
      match msz with
      | Working sz => Ret sz
      | Failed =>
        msz <- Prim td (TD.DiskSize d1);
        match msz with
        | Working sz => Ret sz
        | Failed => Ret 0
        end
      end.

    Definition rd_op_impl T (op: ReplicatedDisk.Op T) : proc T :=
      match op with
      | ReplicatedDisk.Read a => read a
      | ReplicatedDisk.Write a b => write a b
      | ReplicatedDisk.DiskSize => diskSize
      end.

    Fixpoint init_at (a:nat) : proc unit :=
      match a with
      | 0 => Ret tt
      | S a =>
        _ <- Prim td (TD.Write d0 a block0);
        _ <- Prim td (TD.Write d1 a block0);
        init_at a
      end.

    Definition Init : proc InitResult :=
      size <- diskSize;
      _ <- init_at size;
      Ret Initialized.

   (* Recovery tracks what happens at each step in order to implement control
       flow. *)
    Inductive RecStatus :=
    (* continue working, nothing interesting has happened *)
    | Continue
    (* some address has been repaired (or the recovery has exhausted the
       addresses) - only one address can be out of sync and thus only it must be
       recovered. *)
    | RepairDone
    (* one of the disks has failed, so don't bother continuing recovery since the
       invariant is now trivially satisfied *)
    | DiskFailed (i:diskId).

    Definition fixup (a:nat) : proc RecStatus :=
      mv0 <- Prim td (TD.Read d0 a);
      match mv0 with
      | Working v =>
        mv2 <- Prim td (TD.Read d1 a);
        match mv2 with
        | Working v' =>
          if v == v' then
            Ret Continue
          else
            mu <- Prim td (TD.Write d1 a v);
            Ret (match mu with
                 | Working _ => RepairDone
                 | Failed => DiskFailed d1
                 end)
        | Failed => Ret (DiskFailed d1)
        end
      | Failed => Ret (DiskFailed d0)
      end.

    (* recursively performs recovery at [a-1], [a-2], down to 0 *)
    Fixpoint recover_at (a:nat) : proc unit :=
      match a with
      | 0 => Ret tt
      | S n =>
        s <- fixup n;
        match s with
        | Continue =>
          _ <- recover_at n;
          Ret tt
        | RepairDone => Ret tt
        | DiskFailed i => Ret tt
        end
      end.

    Definition Recover : proc unit :=
      sz <- diskSize;
      _  <- recover_at sz;
      Ret tt.

    Definition impl : InterfaceImpl ReplicatedDisk.Op :=
      {| op_impl := rd_op_impl;
         recover_impl := _ <- irec td; Recover;
         init_impl := then_init (iInit td) (Init); |}.

    Definition abstraction_f (td_state : TD.State) : ReplicatedDisk.State :=
      match td_state with
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

    Definition rd_abstraction (state:TD.State) (state':ReplicatedDisk.State) :=
      rd_invariant state /\
      state' = abstraction_f state.

    Definition abstr : Abstraction ReplicatedDisk.State :=
      abstraction_compose
        (interface_abs td)
        {| abstraction := rd_abstraction |}.

    Lemma both_disks_not_missing : forall (state: TD.State),
        TD.disk0 state = None ->
        TD.disk1 state = None ->
        False.
    Proof.
      intros.
      destruct state; simpl; intros.
      destruct disk0, disk1; simpl in *; eauto.
    Qed.

    Lemma rd_abstraction_failure: forall s state state',
      rd_abstraction state s ->
      TD.bg_failure state state' ->
      rd_abstraction state' s.
    Proof.
      intros.
      unfold rd_abstraction, rd_invariant in *.
      unfold abstraction_f in *.
      TD.inv_bg; simpl in *; eauto.
      intuition; subst; auto.
      intuition.
    Qed.

    Lemma rd_abstraction_read: forall s d a v state state',
      rd_abstraction state s ->
      TD.op_step (TD.Read d a) state (Working v) state' ->
      rd_abstraction state' s.
    Proof.
      intros.
      unfold rd_abstraction, rd_invariant in *.
      unfold abstraction_f in *.
      TD.inv_step; simpl in *; eauto.
    Qed.

    Lemma rd_abstraction_read_failure: forall s d a state state',
      rd_abstraction state s ->
      TD.op_step (TD.Read d a) state Failed state' ->
      rd_abstraction state' s.
    Proof.
      intros.
      unfold rd_abstraction, rd_invariant in *.
      unfold abstraction_f in *.
      TD.inv_step; simpl in *; eauto.
    Qed.

    Lemma rd_abstraction_disksize: forall s d v state state',
      rd_abstraction state s ->
      TD.op_step (TD.DiskSize d) state (Working v) state' ->
      rd_abstraction state' s.
    Proof.
      intros.
      unfold rd_abstraction, rd_invariant in *.
      unfold abstraction_f in *.
      TD.inv_step; simpl in *; eauto.
    Qed.

    Lemma rd_abstraction_disksize_failure: forall s d state state',
      rd_abstraction state s ->
      TD.op_step (TD.DiskSize d) state Failed state' ->
      rd_abstraction state' s.
    Proof.
      intros.
      unfold rd_abstraction, rd_invariant in *.
      unfold abstraction_f in *.
      TD.inv_step; simpl in *; eauto.
    Qed.


    Ltac rd_trans := 
      repeat match goal with
      |  [ H : TD.op_step (TD.Read _ _) ?state (Working _) ?state' |- 
           rd_abstraction ?state' _ ] => 
           eapply rd_abstraction_read; [|apply H]
      |  [ H : TD.op_step (TD.Read _ _) ?state Failed ?state' |-
           rd_abstraction ?state' _ ] => 
         eapply rd_abstraction_read_failure; [|apply H]
      |  [ H : TD.bg_failure _ ?state' |- rd_abstraction ?state' _ ] =>
           eapply rd_abstraction_failure; [|apply H]
      | [ H: TD.op_step (TD.DiskSize _) ?state Failed ?state' |-
          rd_abstraction ?state' _ ] =>
          eapply rd_abstraction_disksize_failure; [|apply H]
      end.

    Definition read_disk (state: TD.State) id a v :=
       match (TD.get_disk id state) with
         | Some d =>
             match d a with
             | Some b0 => Working v = Working b0
             | None => exists b : block, Working v = Working b
             end
         | None => Working v = Failed
         end.

    Lemma td_read_ok: forall state id a v s,
      rd_abstraction state s ->
      read_disk state id a v ->
      forall b : block, s a = Some b -> v = b.
    Proof.
      intros.
      unfold read_disk, TD.get_disk in H0.
      unfold rd_abstraction, rd_invariant, abstraction_f in H.
      destruct state; simpl in *.
      destruct disk0; simpl in *.
      - intuition; subst.
        destruct id.
        + destruct (d a).
          inversion H0; auto.
          inversion H1. subst. auto.
          deex. inversion H1.
        + destruct disk1; simpl in *; subst.
          destruct (d0 a); subst.
          inversion H0; subst. inversion H1. auto.
          inversion H1.
          inversion H0.
      - destruct disk1; simpl in *.
        + intuition; subst.
          destruct id.
          inversion H0.
          destruct (d a).
          inversion H0. inversion H1; subst. auto.
          inversion H1.
        + intuition; subst.
    Qed.

    Lemma td_read0_ok: forall state' state'0 s a v,
      rd_abstraction state' s -> 
      TD.op_step (TD.Read d0 a) state'0 (Working v) state' ->
      forall b : block, s a = Some b -> v = b.
    Proof.
      intros.
      TD.inv_step.
      eapply td_read_ok with (id := d0); eauto.
    Qed.

    Lemma td_read1_ok: forall state' state'0 state'1 state'2  s a v,
      rd_abstraction state'1 s ->
      TD.bg_failure state' state'2 ->
      TD.op_step (TD.Read d0 a) state'0 Failed state' ->
      TD.op_step (TD.Read d1 a) state'2 (Working v) state'1 ->
      forall b : block, s a = Some b -> v = b.
    Proof.
      intros.
      TD.inv_step.
      TD.inv_step.
      eapply td_read_ok with (id := d1) (state := state'1); eauto.
    Qed.

    Lemma td_read_none_ok: forall s a state' state'0 state'2 state'1,
      TD.op_step (TD.Read d0 a) state'0 Failed state' ->
      TD.bg_failure state' state'2  ->
      TD.op_step (TD.Read d1 a) state'2 Failed state'1 ->
      forall b : block, s a = Some b -> block0 = b.
    Proof.
      intros.
      TD.inv_step.
      TD.inv_step.
      simpl in *.
      intros.
      case_eq (TD.disk1 state'1); intros.
      rewrite H in H7.
      - destruct (d a).
        -- inversion H7.
        -- deex. inversion H1.
      - case_eq (TD.disk0 state'); intros.
        rewrite H1 in H6.
        -- destruct (d a). inversion H6.
          deex. inversion H3.
        -- 
          inversion H0; subst; eauto.
          ++ 
            apply both_disks_not_missing in H; auto.
            exfalso; auto.
          ++ simpl in *. inversion H.
          ++ simpl in *. inversion H1.
    Qed.

    (* read without recovery *)
    Lemma read_ok: forall a v w w' state s,
      abstraction (interface_abs td) w state ->
      rd_abstraction state s -> 
      exec (read a) w (Finished v w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        (exists state2',
           pre_step ReplicatedDisk.bg_step (@ReplicatedDisk.op_step)
             (ReplicatedDisk.Read a) s v state2' /\
           rd_abstraction state' state2').
    Proof.
      intros.
      inv_exec.
      case_eq v0; intros.
      - (* read from disk 0 *)
        eapply RExec in H7.
        eapply impl_ok in H7; eauto. deex.
        exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
        eexists.
        intuition; eauto.
        eexists s. split.
        eexists s.
        split; eauto.
        constructor.
        constructor.
        eapply td_read0_ok with (state' := state'); eauto.
        rd_trans; auto.
        rd_trans; auto.
        simpl; auto.
      - (* disk 1 failed *)
        rewrite H1 in H9.
        eapply RExec in H7.
        inv_exec.
        case_eq v1; intros.
        rewrite H1 in H11.
        + repeat ( exec_steps || ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          eexists.
          intuition; eauto.
          exists s. split.
          exists s. split; eauto.
          constructor.
          constructor.
          eapply td_read1_ok with (state'1 := state'1); eauto.
          rd_trans; auto.
          rd_trans; auto.
        + (* no working disk *)
          rewrite H1 in H11.
          repeat ( exec_steps || ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          eexists.
          intuition; eauto.
          exists s. split.
          exists s. split. eauto.
          constructor.
          constructor.
          eapply td_read_none_ok; eauto.
          rd_trans; auto.
      Unshelve.
      all: eauto.
    Qed.

    Lemma bg_failure_disk_none: forall id (state:TD.State) state',
      TD.get_disk id state = None ->
      TD.bg_failure state state' ->
      TD.get_disk id state' = None.
    Proof.
      intros.
      TD.inv_bg.
      - eauto.
      - destruct id; simpl in *; eauto.
      - destruct id; simpl in *; eauto.
    Qed.

    Lemma bg_failure_disk_some: forall id (state:TD.State) state' d1 d2,
      TD.get_disk id state = Some d1 ->
      TD.bg_failure state state' ->
      TD.get_disk id state' = Some d2 ->
      d1 = d2.
    Proof.
      intros.
      TD.inv_bg; simpl in *.
      - rewrite H1 in H; eauto. inversion H; auto.
      - destruct id; simpl in *.
        + inversion H1.
        + inversion H1. subst; auto.
          inversion H; auto.
      - destruct id; simpl in *.
        + inversion H1. subst; auto.
          inversion H; auto.
        + inversion H1.
    Qed.

    Lemma bg_failure_disk_both: forall (state:TD.State) state' d1' d2',
      TD.disk0 state' = Some d1' ->
      TD.disk1 state' = Some d2' ->
      TD.bg_failure state state' ->
      TD.disk0 state = TD.disk0 state' /\
      TD.disk1 state = TD.disk1 state'.
    Proof.
      intros. 
      destruct state'.
      destruct state.
      TD.inv_bg; simpl in *.
      - subst; auto.  
      - inversion H.
      - inversion H.
        inversion H0.
    Qed.


    Lemma td_bg_failure: forall (state:TD.State) state' d0 d1,
      TD.bg_failure state state' ->
      TD.disk0 state = Some d0 ->
      TD.disk1 state = Some d1 ->
      (TD.disk0 state' = Some d0 \/ TD.disk0 state' = None) /\
      (TD.disk1 state' = Some d1 \/ TD.disk1 state' = None).
    Proof.
      intros.
      TD.inv_bg; split; eauto.
    Qed.

    Lemma td_bg_failure1: forall (state:TD.State) state' d1,
      TD.bg_failure state state' ->
      TD.disk0 state = None ->
      TD.disk1 state = Some d1 ->
      (TD.disk0 state' = None) /\
      (TD.disk1 state' = Some d1 \/ TD.disk1 state' = None).
    Proof.
      intros.
      TD.inv_bg; split; eauto.
    Qed.

    Lemma td_bg_failure0: forall (state:TD.State) state' d,
        TD.bg_failure state state' ->
        TD.disk0 state = Some d ->
        TD.disk1 state = None ->
        (TD.disk1 state' = None) /\
        (TD.disk0 state' = Some d \/ TD.disk0 state' = None).
    Proof.
      intros.
      TD.inv_bg; split; eauto.
    Qed.

    Lemma td_write0_ok: forall state state' a b d v,
      TD.op_step (TD.Write d0 a b) state v state' ->
      TD.disk0 state = Some d ->
      match v with
         | Working _ => 
            TD.disk0 state' = Some (diskUpd d a b) /\ 
            TD.disk1 state' = (TD.disk1 state)
         | Failed => 
            TD.disk0 state' = None /\ 
            TD.disk1 state' = (TD.disk1 state)
      end.
    Proof.
      intros.
      destruct v; subst; simpl in *.
      - TD.inv_step; simpl in *.
        destruct (TD.disk0 state); subst; simpl in *.
        inversion H0; subst. intuition; auto.
        inversion H; simpl; auto.
        inversion H; simpl; auto.
        inversion H0.
      - TD.inv_step; simpl in *.
        destruct (TD.disk0 state); try congruence.
        intuition; try congruence.
    Qed.

    Lemma td_write1_ok: forall state state' a b d v,
      TD.op_step (TD.Write d1 a b) state v state' ->
      TD.disk1 state = Some d ->
      match v with
         | Working _ => 
            TD.disk0 state' = (TD.disk0 state) /\ 
            TD.disk1 state' = Some (diskUpd d a b)
         | Failed => 
            TD.disk0 state' = (TD.disk0 state) /\ 
            TD.disk1 state' = None
      end.
    Proof.
      intros.
      destruct v; subst; simpl in *.
      - TD.inv_step; simpl in *.
        destruct (TD.disk1 state); subst; simpl in *.
        inversion H0; subst. intuition; auto.
        inversion H; simpl; auto.
        inversion H; simpl; auto.
        inversion H0.
      - TD.inv_step; simpl in *.
        destruct (TD.disk1 state); try congruence.
        intuition; try congruence.
    Qed.

    Lemma td_write_failure: forall d a b state state',
      TD.op_step (TD.Write d a b) state Failed state' ->
      state = state' /\ TD.get_disk d state = None.
    Proof.
      intros.
      unfold rd_abstraction, rd_invariant in *.
      unfold abstraction_f in *.
      TD.inv_step; simpl in *; eauto.
      intuition.
      destruct d; try congruence.
      simpl in *.
      case_eq (TD.disk0 state); intros.
      rewrite H in H6.
      intuition. inversion H1.
      rewrite H in H6.
      intuition; auto.
      simpl in *.
      case_eq (TD.disk1 state); intros.
      rewrite H in H6.
      intuition. inversion H1.
      rewrite H in H6.
      intuition; auto.
      destruct d; try congruence.
      simpl in *.
      case_eq (TD.disk0 state); intros.
      rewrite H in H6.
      intuition. inversion H1.
      rewrite H in H6. auto.
      simpl in *.
      case_eq (TD.disk1 state); intros.
      rewrite H in H6.
      intuition. inversion H1. auto.
    Qed.

    Lemma td_write_none: forall d a b (state:TD.State) state' v,
      TD.get_disk d state = None ->
      TD.op_step (TD.Write d a b) state v state' ->
      state = state'.
    Proof.
      intros.
      TD.inv_step.
      rewrite H in H7.
      intuition; auto.
    Qed.

    Lemma td_write_both_ok: forall s state state' state'' state''' a b,
      rd_abstraction state s ->
      TD.op_step (TD.Write d0 a b) state (Working tt) state' ->
      TD.bg_failure state' state'' ->
      TD.op_step (TD.Write d1 a b) state'' (Working tt) state''' ->
      rd_abstraction state''' (diskUpd s a b).
    Proof.
      intros.
      intuition.
      case_eq (TD.disk0 state); intros.
      + eapply td_write0_ok in H0 as H0'; eauto.
        TD.inv_bg.
        - case_eq (TD.disk1 state); intros.
          -- intuition.
            rewrite H1 in H5.
            eapply td_write1_ok in H5; eauto.
            simpl in *.
            intuition.
            rewrite H4 in H6.
            unfold rd_abstraction, rd_invariant, abstraction_f in *.
            subst; simpl in *.
            destruct state; simpl in *.
            rewrite H3 in H; simpl in *.
            rewrite H1 in H; simpl in *.
            intuition; subst; simpl in *.
            destruct state'''; subst; simpl in *; try congruence.     
            destruct disk0; try congruence.
            destruct disk1; try congruence.
            destruct state'''; subst; simpl in *; try congruence.
            destruct disk0; try congruence.
          -- rewrite H1 in H0'.
            intuition.
            eapply td_write0_ok in H0; eauto. intuition.
            TD.inv_step. simpl in *. rewrite H1 in H7.
            rewrite H7 in H13. intuition. inversion H0.
        - simpl in *.
          case_eq (TD.disk1 state); intros.
          -- intuition. rewrite H1 in H5. inversion H5; subst.
            eapply td_write1_ok in H2; eauto.
            simpl in *. intuition.
            unfold rd_abstraction, rd_invariant, abstraction_f in *.
            destruct state; simpl in *.
            rewrite H3 in H; simpl in *.
            rewrite H1 in H; simpl in *.
            intuition; subst; simpl in *.
            destruct state'''; subst; simpl in *; try congruence.     
            destruct disk0; try congruence.
            destruct disk1; try congruence; auto.
            destruct state'''; subst; simpl in *; try congruence.
            destruct disk0; try congruence.
            destruct disk1; try congruence.
          -- intuition. rewrite H1 in H5. inversion H5; try congruence. 
        - simpl in *. intuition.
          TD.inv_step. simpl in *. intuition. inversion H2.
    + TD.inv_step. TD.inv_step. simpl in *. rewrite H3 in H9.
      intuition; try congruence.
    Qed.

    Lemma td_write_d0_ok: forall s state state' state'' state''' a b,
      rd_abstraction state s ->
      TD.op_step (TD.Write d0 a b) state (Working tt) state' ->
      TD.bg_failure state' state'' ->
      TD.op_step (TD.Write d1 a b) state'' (Failed) state''' ->
      rd_abstraction state''' (diskUpd s a b).
    Proof.
      intros.
      eapply td_write_failure in H2; subst.
      intuition. simpl in *.
      case_eq (TD.disk0 state); intros.
      + eapply td_write0_ok in H0 as H0'; eauto.
        intuition.
        TD.inv_bg.
        - rewrite H4 in H6.
          simpl in *. intuition.
          unfold rd_abstraction, rd_invariant, abstraction_f in *.
          destruct state'''.  simpl in *.
          destruct disk0; try congruence. simpl in *.
          destruct disk1; try congruence. split; auto.
          intuition.
          destruct state.  simpl in *.
          destruct disk0; try congruence. 
        - simpl in *. inversion H4.
        - simpl in *. 
          unfold rd_abstraction, rd_invariant, abstraction_f in *.
          split; auto. inversion H5. 
          intuition.
          destruct state.  simpl in *.
          destruct disk0; try congruence. 
      + subst; simpl in *.
        TD.inv_step.
        simpl in *.
        rewrite H2 in H10. intuition. inversion H0.
    Qed.

    Lemma td_write_d1_ok: forall s state state' state'' state''' a b,
      rd_abstraction state s ->
      TD.op_step (TD.Write d0 a b) state (Failed) state' ->
      TD.bg_failure state' state'' ->
      TD.op_step (TD.Write d1 a b) state'' (Working tt) state''' ->
      rd_abstraction state''' (diskUpd s a b).
    Proof.
      intros.
      eapply td_write_failure in H0; subst.
      intuition. simpl in *.
      case_eq (TD.disk1 state''); intros.
      + TD.inv_bg; simpl in *.
        - eapply td_write1_ok in H0 as H0'; eauto.
          simpl in *. intuition. rewrite H4 in H1.
          unfold rd_abstraction, rd_invariant, abstraction_f in *.
          destruct state'''.  simpl in *.
          destruct disk0; try congruence. simpl in *.
          destruct disk1; try congruence. split; auto.
          inversion H3; auto.
          intuition.
          destruct state''.  simpl in *.
          destruct disk0; try congruence. 
          destruct disk1; try congruence. 
        - eapply td_write1_ok in H2 as H2'; eauto.
          simpl in *. intuition.
          unfold rd_abstraction, rd_invariant, abstraction_f in *.
          destruct state'''.  simpl in *.
          destruct disk0; try congruence.
        - inversion H0.
      + TD.inv_step.
        simpl in *.
        rewrite H0 in H11. intuition.
        inversion H2.
    Qed.

    (* write without recovery *)
    Lemma write_ok: forall a b v w w' state s,
      abstraction (interface_abs td) w state ->
      rd_abstraction state s -> 
      exec (write a b) w (Finished v w') ->
      exists state', 
       abstraction (interface_abs td) w' state' /\
       (exists state2',
          pre_step ReplicatedDisk.bg_step (@ReplicatedDisk.op_step)
           (ReplicatedDisk.Write a b) s v state2' /\ rd_abstraction state' state2').
    Proof.
      intros.
      repeat ( exec_steps || ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
      eapply rd_abstraction_failure in b0 as b0'; eauto.
      destruct v0.
      - destruct v1.
        + destruct v.
          destruct v0.
          eapply td_write_both_ok with (state := state'0) (state''' := state'1) in H3 as Hrd; eauto.
          eexists. split; eauto.
          exists (diskUpd s a b).
          split; eauto.
          eexists.
          split.
          constructor.
          constructor.
        + destruct v.
          eapply td_write_d0_ok with (state := state'0) (state''' := state'1) in o; eauto.
          eexists. split; eauto.
          exists (diskUpd s a b).
          split; eauto.
          eexists.
          split.
          constructor.
          constructor.
    - destruct v1. destruct v. 
      eapply td_write_d1_ok with (state''' := state'1) in H3 as H3'; eauto.
      + eexists. split; eauto.
        exists (diskUpd s a b).
        split; eauto.
        eexists.
        split.
        constructor.
        constructor.
      + eapply td_write_failure in o.
        eapply td_write_failure in H3.
        intuition. subst; simpl in *.
        TD.inv_bg; simpl in *.
        -- unfold rd_abstraction, rd_invariant, abstraction_f in b0'.
          destruct state'1; simpl in *.
          destruct disk0; try congruence.
          destruct disk1; try congruence. intuition.
        -- unfold rd_abstraction, rd_invariant, abstraction_f in b0'.
          intuition.
        -- unfold rd_abstraction, rd_invariant, abstraction_f in b0'.
          intuition. subst.
          destruct pf; auto.
      Unshelve.
      all: eauto.
    Qed.


    Definition disk_size (state: TD.State) id v :=
      match TD.get_disk id state with
      | Some d => Working v = Working (size d)
      | None => Working v = Failed
      end.

    Lemma td_disk_size_ok: forall s state id v,
      rd_abstraction state s ->
      disk_size state id v ->
      v = (@size block s).
    Proof.
      intros.
      unfold disk_size in *; simpl in *.
      unfold rd_abstraction, rd_invariant, abstraction_f in H.
      destruct state; simpl in *.
      destruct disk0; simpl in *.
     - intuition; subst.
        destruct id.
        + simpl in *.
          inversion H0; auto.
        + simpl in *.
          destruct disk1; try congruence.
     - intuition; simpl in *.
       destruct id.
        + simpl in *.
          inversion H0; auto.
        + simpl in *.
          destruct disk1; try congruence.
    Qed.

    Definition disk_size_failed (state: TD.State) id :=
      match TD.get_disk id state with
      | Some d => Failed = Working (size d)
      | None => @Failed nat = Failed
      end.

    Lemma td_disk_size_none_ok: forall state' state'2,
      disk_size_failed state' d0 ->
      TD.bg_failure state' state'2  ->
      disk_size_failed state'2 d1 ->
      False.
    Proof.
      unfold disk_size_failed; simpl; intros.
      case_eq (TD.disk1 state'2); intros.
      - rewrite H2 in H1. inversion H1.
      - case_eq (TD.disk0 state'); intros.
        + rewrite H3 in H. inversion H.
        + rewrite H3 in H.
          TD.inv_bg; simpl in *; try congruence.
          apply both_disks_not_missing in H2; auto.
    Qed.

    (* disk size without recovery *)
    Lemma disk_size_ok: forall v w w' state s,
      abstraction (interface_abs td) w state ->
      rd_abstraction state s -> 
      exec diskSize w (Finished v w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        (exists state2',
           pre_step ReplicatedDisk.bg_step (@ReplicatedDisk.op_step)
             ReplicatedDisk.DiskSize s v state2' /\
           rd_abstraction state' state2').
    Proof.
      intros.
      repeat ( exec_steps || TD.inv_step ).
      - eapply td_disk_size_ok with (s := s) (id := d0) in H6.
        eexists. split; eauto.
        exists s.
        split; eauto.
        eexists.
        split.
        constructor.
        subst.
        constructor.
        rd_trans. auto.
        rd_trans. auto.
      - eapply td_disk_size_ok with (s := s) (id := d1) in H6.
        eexists. split; eauto.
        exists s.
        split; eauto.
        eexists.
        split.
        constructor.
        subst.
        constructor.
        rd_trans. auto.
        rd_trans. auto.
      - exfalso.
        eapply td_disk_size_none_ok; eauto.
    Unshelve.
      all: eauto.
    Qed.

    Definition td_disk_size_post (state:TD.State) v :=
      match (TD.get_disk d0 state, TD.get_disk d1 state) with
      | (Some d', Some d'') => size d' = v /\ size d'' = v
      | (Some d', None) => size d' = v
      | (None, Some d'') => size d'' = v
      | (None, None) => False
      end.

    (* The disk is synchronous so at most one address that is out of sync. *)
    Definition recovery_pre (state: TD.State) sold snew a' :=
      ( snew = sold /\
        match (TD.get_disk d0 state, TD.get_disk d1 state) with
        | (Some d', Some d'') => d' = sold /\ d'' = sold
        | (Some d', None) => d' = sold
        | (None, Some d'') => d'' = sold
        | (_, _) => False
        end ) \/
      ( exists a b, snew = diskUpd sold a b /\
        match (TD.get_disk d0 state, TD.get_disk d1 state) with
        | (Some d', Some d'') =>
          (d' = sold /\ d'' = sold) \/
          (d' = snew /\ d'' = sold /\ a < a') \/
          (d' = snew /\ d'' = snew)
        | (Some d', None) =>
          d' = sold \/ d' = snew
        | (None, Some d'') =>
          d'' = sold \/ d'' = snew
        | (_, _) => False  (* one disk must be working *)
        end ).

    Lemma bg_failure_ok: forall id d (state:TD.State) state',
      TD.get_disk id state' = Some d ->
      TD.bg_failure state state' ->
      TD.get_disk id state = Some d.
    Proof.
      intros.
      destruct id; simpl in *.
      - TD.inv_bg; simpl in *; auto.
        + try congruence.
      - TD.inv_bg; simpl in *; auto.
        + try congruence.
    Qed.

    Lemma fixup_eq_ok: forall (state state' state'0 : TD.State) sold snew v b,
      recovery_pre state sold snew (S v) ->
      v < size sold ->
      TD.bg_failure state state' ->
      match TD.get_disk d0 state' with
      | Some d =>
          match d v with
          | Some b0 => Working b = Working b0
          | None => exists b0 : block, Working b = Working b0
          end
      | None => Working b = Failed
      end ->
      TD.bg_failure state' state'0 ->
      match TD.get_disk d1 state'0 with
           | Some d =>
               match d v with
               | Some b0 => Working b = Working b0
               | None => exists b0 : block, Working b = Working b0
               end
           | None => Working b = Failed
           end ->
      recovery_pre state'0 sold snew v.
    Proof.
      intros.

      unfold recovery_pre in *; intros.

      case_eq (TD.get_disk TwoDiskAPI.d0 state'); [ intros ? He; rewrite He in * | intro He; rewrite He in *; congruence ].
      case_eq (TD.get_disk TwoDiskAPI.d1 state'0); [ intros ? He2; rewrite He2 in * | intro He2; rewrite He2 in *; congruence ].

      repeat match goal with
      | Hb : TD.bg_failure _ ?state,
        Hd : TD.get_disk _ ?state = Some _ |- _ =>
        eapply bg_failure_ok in Hd; [ | exact Hb ];
        try rewrite Hd in *
      end.

      intuition.

      - (* Both disks the same, from [recovery_pre]. *)
        left. intuition.
        case_eq (TD.get_disk TwoDiskAPI.d0 state'0); intuition eauto.

        repeat match goal with
        | Hb : TD.bg_failure _ ?state,
          Hd : TD.get_disk _ ?state = Some _ |- _ =>
          eapply bg_failure_ok in Hd; [ | exact Hb ];
          try rewrite Hd in *
        end.
        congruence.

      - (* Disks differ, from [recovery_pre]. *)
        repeat deex.
        right.

        do 2 eexists; intuition.

        + (* Both disks are old. *)
          case_eq (TD.get_disk TwoDiskAPI.d0 state'0); intuition eauto.
          repeat match goal with
          | Hb : TD.bg_failure _ ?state,
            Hd : TD.get_disk _ ?state = Some _ |- _ =>
            eapply bg_failure_ok in Hd; [ | exact Hb ];
            try rewrite Hd in *
          end.

          left; intuition eauto.
          congruence.

        + (* Disks differ on some sector. *)
          case_eq (TD.get_disk TwoDiskAPI.d0 state'0); intuition eauto.
          repeat match goal with
          | Hb : TD.bg_failure _ ?state,
            Hd : TD.get_disk _ ?state = Some _ |- _ =>
            eapply bg_failure_ok in Hd; [ | exact Hb ];
            try rewrite Hd in *
          end.

          inversion He; subst.

          destruct (lt_dec a v).

          * right. left. eauto.
          * left; intuition.
            assert (a = v) by omega; subst.
            autorewrite with upd in *.
            inversion H2; subst.

            rewrite diskUpd_same; eauto.
            case_eq (sold v); intros.
            { rewrite H in *; congruence. }

            exfalso.
            eapply disk_inbounds_not_none; eauto.

        + (* Both disks are new. *)
          case_eq (TD.get_disk TwoDiskAPI.d0 state'0); intuition eauto.
          repeat match goal with
          | Hb : TD.bg_failure _ ?state,
            Hd : TD.get_disk _ ?state = Some _ |- _ =>
            eapply bg_failure_ok in Hd; [ | exact Hb ];
            try rewrite Hd in *
          end.

          right; right; intuition eauto.
          congruence.
    Qed.


    (* fix up for v that isn't out of sync. keep repairing *)
    Lemma fixup_continue_ok: forall v w w' (state: TD.State) sold snew,
      recovery_pre state sold snew (S v) ->
      v < size sold ->
      abstraction (interface_abs td) w state ->
      exec (fixup v) w (Finished Continue w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' sold snew v.
    Proof.
      intros.
      repeat ( exec_steps || TD.inv_step ).
      all: try congruence.

      - eapply fixup_eq_ok in H; eauto.
      - destruct v0; congruence.

    Unshelve.
      all: auto.
    Qed.


    (* fix up for v that is out of sync, repair and be done *)
    Lemma fixup_repair_ok: forall v w w' (state: TD.State) sold snew,
      recovery_pre state sold snew (S v) ->
      v < size sold ->
      abstraction (interface_abs td) w state ->
      exec (fixup v) w (Finished RepairDone w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' sold snew 0.
    Proof.
      intros.
      repeat ( exec_steps || TD.inv_step ).
      all: try congruence.

      unfold recovery_pre in *; intros.

      destruct v0; try congruence.

      replace (TD.disk0 state') with (TD.get_disk TwoDiskAPI.d0 state') in * by reflexivity.
      replace (TD.disk1 state'1) with (TD.get_disk TwoDiskAPI.d1 state'1) in * by reflexivity.
      replace (TD.disk1 state'4) with (TD.get_disk TwoDiskAPI.d1 state'4) in * by reflexivity.

      case_eq (TD.get_disk TwoDiskAPI.d0 state'); [ intros ? He; rewrite He in * | intro He; rewrite He in *; congruence ].
      case_eq (TD.get_disk TwoDiskAPI.d1 state'1); [ intros ? He2; rewrite He2 in * | intro He2; rewrite He2 in *; congruence ].
      case_eq (TD.get_disk TwoDiskAPI.d1 state'4); [ intros ? He3; rewrite He3 in * | intro He3; rewrite He3 in *; intuition congruence ].

      repeat match goal with
      | Hb : TD.bg_failure _ ?state,
        Hd : TD.get_disk _ ?state = Some _ |- _ =>
        eapply bg_failure_ok in Hd; [ | exact Hb ];
        try rewrite Hd in *
      end.

      eexists. split; eauto.

      replace d1 with d0 in * by congruence.
      intuition.

      - (* Original disks were the same. Impossible because we found a difference. *)
        exfalso.
        subst.

        case_eq (sold v); intros.
        + rewrite H in *; congruence.
        + eapply disk_inbounds_not_none; eauto.

      - (* Original disks differed. *)
        repeat deex.
        right.
        do 2 eexists; intuition.

        + (* Both disks were same: again, impossible. *)
          exfalso.
          subst.

          case_eq (sold v); intros.
          * rewrite H in *; congruence.
          * eapply disk_inbounds_not_none; eauto.

        + (* Disks differed, finally. Is it this address, though? *)
          destruct (a0 == v); subst.
          * subst; simpl.
            autorewrite with upd in *.
            replace b0 with v1 in * by congruence.
            replace (TD.disk0 state'4) with (TD.get_disk TwoDiskAPI.d0 state'4) by reflexivity.

            case_eq (TD.get_disk TwoDiskAPI.d0 state'4); intros; eauto.
            repeat match goal with
            | Hb : TD.bg_failure _ ?state,
              Hd : TD.get_disk _ ?state = Some _ |- _ =>
              eapply bg_failure_ok in Hd; [ | exact Hb ];
              try rewrite Hd in *
            end.

            inversion He; subst. eauto.

          * exfalso.
            autorewrite with upd in *.
            case_eq (sold v); intros.
           -- rewrite H in *; congruence.
           -- eapply disk_inbounds_not_none; eauto.

        + (* Both disks were same: again, impossible. *)
          exfalso.
          subst.

          case_eq ((diskUpd sold a0 b0) v); intros.
          * rewrite H in *; congruence.
          * destruct (a0 == v); subst.
            autorewrite with upd in *; congruence.
            autorewrite with upd in *.
            case_eq (sold v); intros.
           -- rewrite H in *; congruence.
           -- eapply disk_inbounds_not_none; eauto.

    Unshelve.
      all: eauto.
    Qed.

    (* fix up for v that is out of sync, repair and be done *)
    Lemma fixup_repair_failure: forall v w w' (state: TD.State) sold snew i,
       recovery_pre state sold snew (S v) ->
       v < size sold ->
       abstraction (interface_abs td) w state ->
       exec (fixup v) w (Finished (DiskFailed i) w') ->
       exists state',
         abstraction (interface_abs td) w' state' /\
         recovery_pre state' sold snew 0.
    Proof.
      intros.
      repeat ( exec_steps || TD.inv_step ).
      all: try congruence.

    Admitted.


    Lemma recover_at_ok: forall v w w' state sold snew,
      recovery_pre state sold snew v ->
      v <= size sold ->
      abstraction (interface_abs td) w state ->
      exec (recover_at v) w (Finished tt w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' sold snew 0.
    Proof.
      induction v; intros.
      - exists state.
        inv_exec.
        split; auto.
      - inv_exec.
        destruct v0.
        + eapply fixup_continue_ok in H8 as H8'; eauto; try omega.
          deex.
          specialize (IHv w'0 w' state' sold snew).
          edestruct IHv; eauto; try omega.
          inv_exec; destruct v0; eauto.
        + inv_exec.
          eapply fixup_repair_ok in H8 as H8'; eauto.
        + inv_exec.
          eapply fixup_repair_failure in H8 as H8'; eauto.
    Qed.

    Definition td_disk_size_pre (state:TD.State) :=
      match (TD.get_disk d0 state, TD.get_disk d1 state) with
      | (Some d', Some d'') => d' = d'' /\ size d' = size d''
      | (Some d', None) => True
      | (None, Some d'') => True
      | (None, None) => False
      end.

    Lemma recovery_pre_failure: forall state state' sold snew n,
      recovery_pre state n sold snew ->
      TD.bg_failure state state' ->
      recovery_pre state' n sold snew.
    Proof.
      intros.
      TD.inv_bg.
      + auto.
      + unfold recovery_pre in *; simpl in *.
        intuition.
        repeat deex.
        intuition; subst.

        * right. do 2 eexists. eauto.
        * right. do 2 eexists. eauto.
        * right. do 2 eexists. eauto.

      + unfold recovery_pre in *; simpl in *.
        intuition.
        repeat deex.
        intuition.

        * right. do 2 eexists. eauto.
        * right. do 2 eexists. eauto.
        * right. do 2 eexists. eauto.
    Qed.


    (* disk size on post-crash, pre-recovery state *)
    Lemma disk_size_ok': forall v w w' state sold snew,
      abstraction (interface_abs td) w state ->
      recovery_pre state sold snew (size sold) ->
      exec diskSize w (Finished v w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        td_disk_size_post state' v /\
        recovery_pre state' sold snew (size sold).
    Proof.
      intros.
      repeat ( exec_steps || TD.inv_step ).

      all: repeat ( eapply recovery_pre_failure in H0; [ | eassumption ] ).
      all: eexists; intuition eauto.

      - unfold td_disk_size_post; simpl.
        unfold recovery_pre in *; simpl in *.
        destruct (TD.disk0 state'); destruct (TD.disk1 state'); try congruence.

        intuition; subst; try congruence.
        repeat deex; intuition; subst; try congruence.
        autorewrite with upd in *. congruence.

      - unfold td_disk_size_post; simpl.

        replace (TD.disk0 state') with (TD.get_disk TwoDiskAPI.d0 state') in * by reflexivity.
        case_eq (TD.get_disk TwoDiskAPI.d0 state'1); intros.

        repeat match goal with
        | Hb : TD.bg_failure _ ?state,
          Hd : TD.get_disk _ ?state = Some _ |- _ =>
          eapply bg_failure_ok in Hd; [ | exact Hb ];
          try rewrite Hd in *
        end.
        congruence.

        simpl in *.
        destruct (TD.disk0 state'1); destruct (TD.disk1 state'1); try congruence.

      - case_eq (TD.disk0 state'); [ intros ? He; rewrite He in *; congruence | ].
        case_eq (TD.disk1 state'1); [ intros ? He; rewrite He in *; congruence | ].
        intros.

        replace (TD.disk0 state') with (TD.get_disk TwoDiskAPI.d0 state') in * by reflexivity.
        eapply bg_failure_disk_none in H4; eauto.
        simpl in *.

        exfalso.
        eapply both_disks_not_missing; eauto.

    Unshelve.
      all: eauto.
    Qed.

    Lemma recover_finish_ok: forall w w' sold snew state,
      abstraction (interface_abs td) w state ->
      recovery_pre state sold snew (size sold) ->
      exec Recover w (Finished tt w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' sold snew 0.
    Proof.
      intros.
      inv_exec.
      inv_exec.
      destruct v0.

      eapply disk_size_ok' with (state := state) in H7; eauto.
      deex.

      cut (v = size sold); intros; subst.
      eapply recover_at_ok with (state := state') in H6; eauto.

      unfold td_disk_size_post in H3.
      unfold recovery_pre in H4.
      simpl in *.

      destruct (TD.disk0 state'); destruct (TD.disk1 state'); intuition; try congruence.
      all: repeat deex; intuition; try congruence; subst.
      all: autorewrite with upd in *; eauto.
    Qed.


    (* read with recovery *)
    Lemma read_recover_ok: forall s a w state w' w'' w''',
      abstraction (interface_abs td) w state ->
      rd_abstraction state s ->
      exec (read a) w (Crashed w') -> 
      exec (irec td) (world_crash w') (Finished tt w'') ->
      exec Recover w'' (Finished tt w''') ->
      exists state',
        abstraction (interface_abs td) w''' state' /\
        (exists state2', (tt = tt /\ (state2' = s \/
          (exists state1 v,
           pre_step ReplicatedDisk.bg_step (@ReplicatedDisk.op_step)
             (ReplicatedDisk.Read a) s v state1 /\ state2' = state1))) /\
           rd_abstraction state' state2').
    Proof.
      intros.
    Admitted.

    Lemma rd_abstraction_recovery_pre: forall state s,
      rd_abstraction state s ->
      recovery_pre state s s (size s).
    Proof.
(*
      unfold rd_abstraction, rd_invariant, abstraction_f, recovery_pre in *.
      intros. simpl in *.
      case_eq (TD.disk0 state); intros.
      + case_eq (TD.disk1 state); intros.
        - destruct state. simpl in *.
          rewrite H1 in H.
          rewrite H2 in H.
          intuition; subst; simpl in *.
          left. split; auto.
        - destruct state. simpl in *.
          rewrite H1 in H.
          rewrite H2 in H.
          intuition; subst; simpl in *.
      + case_eq (TD.disk1 state); intros.
        - destruct state. simpl in *.
          rewrite H1 in H.
          rewrite H2 in H.
          intuition; subst; simpl in *.
        - destruct state. simpl in *.
          rewrite H1 in H.
          rewrite H2 in H.
          intuition; subst; simpl in *.
*)
    Admitted.


    Ltac recovery_pre := repeat match goal with
      | [ |- 
          recovery_pre ?s _ _ ] => unfold recovery_pre; intros; simpl
      | [ H: TD.disk0 ?s = _ |- match TD.disk0 ?s with _ => _ end ] =>
          rewrite H
      | [ H: TD.disk1 ?s = _ |- match TD.disk1 ?s with _ => _ end ] =>
        rewrite H
      | [ H1: TD.disk0 ?s = None, H2: TD.disk1 ?s = None |- _ ] =>
        idtac "x"; eapply both_disks_not_missing; eauto
      end.

(*
    Lemma write0_crash_ok: forall a b v state state' s,
      rd_abstraction state s ->
      TD.op_step (TD.Write d0 a b) state v state' ->
      recovery_pre state' s (size s).
    Proof.
      intros.
      destruct state.
      destruct disk0.
      + destruct disk1.
        - assert (s = d /\ d = d0).
          unfold rd_abstraction, rd_invariant, abstraction_f  in H; eauto.
          intuition; subst. intuition. subst.
          destruct v.  
          ++ eapply td_write0_ok in H0; eauto; try reflexivity.
            intuition; simpl in *.
            recovery_pre; right. exists a, b; split; auto; admit. 
          ++ eapply td_write_failure in H0; eauto; try reflexivity.
            intuition; simpl in *.
        - assert (s = d).
          unfold rd_abstraction, rd_invariant, abstraction_f  in H; eauto.
          intuition; subst. intuition. subst.
          destruct v.
          ++ eapply td_write0_ok in H0; eauto; try reflexivity.
            intuition; simpl in *.
            recovery_pre; right. exists a, b; split; auto; admit. 
          ++ eapply td_write_failure in H0; eauto; try reflexivity.
            intuition; simpl in *.
      + destruct disk1.
        assert (s = d).
        unfold rd_abstraction, rd_invariant, abstraction_f  in H; eauto.
        intuition; subst. intuition. subst.
        - eapply td_write_none in H0; eauto; try reflexivity.
          subst.
          recovery_pre; right. exists a, b; split; auto; admit. 
        - eapply td_write_none in H0; eauto; try reflexivity. 
          exfalso. eapply both_disks_not_missing with (state := state'); subst; eauto.
    Admitted.
*)

(*
    Lemma write_both_crash_ok: forall a b v v0 state state' state'0 state'1 s,
      rd_abstraction state s -> 
      TD.op_step (TD.Write d0 a b) state v state' ->
      TD.bg_failure state' state'1 ->
      TD.op_step (TD.Write d1 a b) state'1 v0 state'0 ->
      recovery_pre state'0 s (size s).
    Proof.
      intros.
      destruct state.
      destruct disk0.
      + destruct disk1.
        - assert (d = d0 /\ s = d).
          unfold rd_abstraction, rd_invariant, abstraction_f  in H; eauto.
          intuition; subst.
          destruct v.
          ++ eapply td_write0_ok in H0; simpl in *; eauto. intuition.
            eapply td_bg_failure in H1; eauto.
            intuition.
            --- destruct v0.
              eapply td_write1_ok in H2; eauto. intuition; simpl in *.
              recovery_pre; right. exists a, b; split; auto; admit.
              eapply td_write_failure in H2;eauto. intuition; simpl in *; subst.
              recovery_pre; right. exists a, b; split; auto; admit.
            ---
              eapply td_write_none with (d := d1) in H2; eauto; subst.
              recovery_pre; right. exists a, b; split; auto; admit.
            --- 
              destruct v0.
              +++ eapply td_write1_ok in H2; eauto. intuition; simpl in *.
                recovery_pre; right. exists a, b; split; auto; admit.
              +++ eapply td_write_failure in H2;eauto. intuition; simpl in *; subst.
                 exfalso. recovery_pre.
            --- exfalso. recovery_pre.
          ++ 
            eapply td_write_failure in H0;eauto. intuition; simpl in *; subst.
        - assert (s = d).
          unfold rd_abstraction, rd_invariant, abstraction_f  in H; eauto.
          intuition; auto.
          subst.
          destruct v.
          ++ eapply td_write0_ok in H0; eauto; try reflexivity. 
            intuition; simpl in *; subst.
            eapply td_bg_failure0 in H1; eauto.
            intuition.
            ---  eapply td_write_none in H2;eauto. intuition; simpl in *; subst.
              recovery_pre; right. exists a, b; split; auto; admit.
            --- exfalso. recovery_pre.
          ++ eapply td_write_failure in H0;eauto. intuition; simpl in *; subst.
      + destruct disk1.
        - assert (d = s).
          unfold rd_abstraction, rd_invariant, abstraction_f  in H; eauto.
          intuition; auto. subst.
          eapply td_write_none in H0;eauto. intuition; simpl in *; subst.
          eapply td_bg_failure1 in H1; eauto; try reflexivity.
          intuition.
          ++ destruct v0.
            -- eapply td_write1_ok in H2; eauto. intuition; simpl in *.
              recovery_pre; right. exists a, b; split; auto; admit.
            -- eapply td_write_failure in H2;eauto. intuition; simpl in *; subst.
              recovery_pre.
          ++ exfalso. recovery_pre.
        - eapply td_write_none in H0; eauto; try reflexivity. 
          exfalso. eapply both_disks_not_missing with (state := state'); subst; eauto.
    Admitted.
*)

    (* write with crash *)
    Lemma write_crash_ok: forall a b w w' state sold,
      abstraction (interface_abs td) w state ->
      rd_abstraction state sold -> 
      rexec (write a b) (irec td) w (Recovered tt w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' sold (diskUpd sold a b) (size sold).
    Proof.
      intros.

unfold write in H1.

Search proc_spec Bind.

    Lemma rexec_bind_recovered : forall T T2 R (p1 : proc T) (p2 : T -> proc T2) (rec : proc R) w w' (res : R),
      rexec (Bind p1 p2) rec w (Recovered res w') ->
      (rexec p1 rec w (Recovered res w')) \/
      (exists w'' res'',
       rexec p1 rec w (RFinished res'' w'') /\
       rexec (p2 res'') rec w'' (Recovered res w')).
    Proof.
      intros.
      inversion H.
      inv_exec.
      - left. econstructor; eauto.
      - right. exists w'1, v. split.
        econstructor; eauto.
        econstructor; eauto.
      - left. econstructor; eauto.
    Qed.

    Lemma rexec_bind : forall T T2 R (p1 : proc T) (p2 : T -> proc T2) (rec : proc R) w out,
      rexec (Bind p1 p2) rec w out ->
      exists out',
      rexec p1 rec w out' /\
      ((exists res w',
        out' = Recovered res w' /\
        out  = Recovered res w') \/
       (exists res w',
        out' = RFinished res w' /\
        rexec (p2 res) rec w' out)).
    Proof.
      
    Admitted.

      eapply rexec_bind in H1. deex.
      eapply impl_ok in H1; eauto; unfold pre; simpl; eauto.

      destruct out'; intuition; repeat deex; try congruence.

      - (* p1 finishes *)
        simpl in *. unfold pre_step in H4. deex. TD.inv_step.

        (* consider p2 ..... *)
        admit.

      - (* p1 never finishes *)
        simpl in *. unfold pre_step in H4. intuition; repeat deex.
        (* p1 crashed before anything.. *)
        admit.

        (* p1 crashed after the write *)
        admit.



Check impl_ok.

      - exists state.
        split; auto.
(*
        apply rd_abstraction_recovery_pre; auto.
*)
        admit.
      - exec_step.
        exec_step; deex.
        simpl in *; unfold pre_step in *; repeat deex.
        TD.inv_step.

        exec_step.
        + eapply rd_abstraction_failure in H0; eauto.
          admit.

        + exec_step.
          exec_step; deex.
          simpl in *; unfold pre_step in *; repeat deex.
          TD.inv_step.

          eexists; intuition eauto.
          admit.

        + eapply RExecCrash in H8.
          eapply impl_ok in H8; eauto; simpl; eauto.



 eapply RExec in H8.
          eapply impl_ok in H8; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          apply rd_abstraction_failure with (s:=s) in H2; auto.
          exists state'0. split; auto.
          eapply write_both_crash_ok with (s := s) (state := state'2) in H6; eauto.
          simpl; auto.
        + admit.
        + simpl; auto.
      - admit.
    Unshelve. all: auto.
    Admitted.

    Lemma irec_recover_ok: forall w' w'',
        exec (@irec TD.Op TD.State TD.API td) (world_crash w') (Finished tt w'') ->
        w' = w''.
    Proof.
        intros.
        destruct td.
        unfold irec in *. simpl in *.
        (* XXX probably boils down to TD.wipe, which promises states are equal *)
        (* XXX maybe need some composable recovery theorem. *)
    Admitted.

    Lemma recovery_pre0_rd_abstraction: forall state s,
      recovery_pre state s 0 ->
      rd_abstraction state s.
    Proof.
      intros.
      unfold rd_abstraction, rd_invariant, abstraction_f, recovery_pre in *.
      intros. simpl in *.
      case_eq (TD.disk0 state); intros.
      + case_eq (TD.disk1 state); intros.
        - destruct state. simpl in *.
          rewrite H1 in *.
          rewrite H0 in *.
          assert (0 <= size s) by omega.
          specialize (H H2).
          intuition; subst; simpl in *; auto.
          repeat deex.
          intuition.
          repeat deex.
          intuition.
        - destruct state. simpl in *.
          rewrite H1 in *.
          rewrite H0 in *.
          intuition; subst; simpl in *.
          assert (0 <= size s) by omega.
          specialize (H H0).
          intuition; subst; simpl in *; auto.
          repeat deex.
          intuition.
       + case_eq (TD.disk1 state); intros.
        - destruct state. simpl in *.
          rewrite H1 in *.
          rewrite H0 in *.
          assert (0 <= size s) by omega.
          specialize (H H2).
          intuition; subst; simpl in *; auto.
          repeat deex.
          intuition.
        - destruct state. simpl in *.
          rewrite H1 in H.
          rewrite H0 in H.
          intuition; subst; simpl in *.
    Qed.

    Lemma write_recover_ok: forall s a b w state w''',
      abstraction (interface_abs td) w state ->
      rd_abstraction state s ->
      rexec (write a b) (_ <- irec td; Recover) w (Recovered tt w''') ->
      exists state' : TD.State,
       abstraction (interface_abs td) w''' state' /\
        (exists state2', (tt = tt /\ (state2' = s \/
            (exists state1 v,
                op_sem ReplicatedDisk.API (ReplicatedDisk.Write a b) s v state1 /\ 
                state2' = state1))) /\ rd_abstraction state' state2').
    Proof.
      intros.
      unfold op_sem; simpl.
      eapply write_crash_ok in H1; eauto. deex.
      eapply irec_recover_ok in H2; eauto. subst.
      eapply recover_finish_ok in H3; eauto. deex.
      exists state'0.
      split; auto.
      exists s.
      split; auto.
      apply recovery_pre0_rd_abstraction in H3; auto.
    Qed.

    Definition rd : Interface ReplicatedDisk.API.
      unshelve econstructor.
      - exact impl.
      - exact abstr.
      - intros.
        destruct op; unfold op_spec;
          apply spec_abstraction_compose;
            unfold spec_impl, abstr.
        + (* Read *)
          unfold proc_spec; intros.
          destruct a0; simpl in *; intuition.
          inv_rexec.
          -- (* no recovery *)
            eapply read_ok; eauto.
          -- (* w. recovery *)
            destruct H4.
            ++ (* run recovery once *)
              inv_exec.
              destruct v. simpl in *.
              destruct v0.
              eapply read_recover_ok; eauto.
            ++ (* crash during recovery, run recovery again *)
              admit.
        + (* Write *)
          unfold proc_spec; intros.
          destruct a0; simpl in *; intuition.
          inv_rexec.
          -- eapply write_ok; eauto.
          -- destruct H4.
            ++ inv_exec.
              destruct v. simpl in *.
              destruct v0.
              eapply write_recover_ok; eauto.
            ++ (* crash during recovery, run recovery again *)
              admit.
        + (* diskSize *)
          unfold proc_spec; intros.
          destruct a; simpl in *; intuition.
          inv_rexec.
          -- (* wo recovery *)
            eapply disk_size_ok; eauto.
          -- admit.
    - admit. 
    - admit.

      Unshelve.
      all: eauto.

    Defined.

  End Implementation.

End RemappedDisk.
