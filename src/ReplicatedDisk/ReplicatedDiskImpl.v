Require Import Automation.
Require Import Disk.SimpleDisk.
Require Import Omega.

Require Import ReplicatedDisk.ReplicatedDiskAPI.
Require Import ReplicatedDisk.TwoDiskAPI.

Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.


Module ReplicatedDisk.

  Section Implementation.

    Variable (td : Interface TD.API).

    Definition read (a:addr) : prog block :=
      mv0 <- Prim td (TD.Read d0 a);
        match mv0 with
        | Working v => Ret v
        | Failed => mv2 <- Prim td (TD.Read d1 a);
                     match mv2 with
                     | Working v => Ret v
                     | Failed => Ret block0
                     end
        end.

    Definition write (a:addr) (b:block) : prog unit :=
      _ <- Prim td (TD.Write d0 a b);
        _ <- Prim td (TD.Write d1 a b);
        Ret tt.

    Definition diskSize : prog nat :=
      msz <- Prim td (TD.DiskSize d0);
        match msz with
        | Working sz => Ret sz
        | Failed => msz <- Prim td (TD.DiskSize d1);
                     match msz with
                     | Working sz => Ret sz
                     | Failed => Ret 0
                     end
        end.


    Definition rd_op_impl T (op: ReplicatedDisk.Op T) : prog T :=
      match op with
      | ReplicatedDisk.Read a => read a
      | ReplicatedDisk.Write a b => write a b
      | ReplicatedDisk.DiskSize => diskSize
      end.

    Fixpoint init_at (a:nat) : prog unit :=
      match a with
      | 0 => Ret tt
      | S a => _ <- Prim td (TD.Write d0 a block0);
                _ <- Prim td (TD.Write d1 a block0);
                init_at a
      end.

    Definition DiskSizes : prog (nat * nat + nat) :=
      sz1 <- Prim td (TD.DiskSize d0);
        match sz1 with
        | Working sz1 => sz2 <- Prim td (TD.DiskSize d1);
                          match sz2 with
                          | Working sz2 => if sz1 == sz2 then
                                            Ret (inr sz1)
                                          else Ret (inl (sz1, sz2))
                          | Failed => Ret (inr sz1)
                          end
        | Failed => sz2 <- Prim td (TD.DiskSize d1);
                     match sz2 with
                     | Working sz2 => Ret (inr sz2)
                     | Failed => Ret (inl (0, 0)) (* impossible *)
                     end
        end.

    Definition Init : prog InitResult :=
      sizes <- DiskSizes;
        match sizes with
        | inr sz => _ <- init_at sz;
                     Ret Initialized
        | inl _ => Ret InitFailed
        end.

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

    Definition fixup (a:addr) : prog RecStatus :=
      mv0 <- Prim td (TD.Read d0 a);
        match mv0 with
        | Working v => mv2 <- Prim td (TD.Read d1 a);
                        match mv2 with
                        | Working v' => if v == v' then
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
    Fixpoint recover_at (a:addr) : prog RecStatus :=
      match a with
      | 0 => Ret RepairDone
      | S n => s <- fixup n;
                match s with
                | Continue => recover_at n
                | RepairDone => Ret RepairDone
                | DiskFailed i => Ret (DiskFailed i)
                end
      end.

    Definition Recover : prog unit :=
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
        + eapply impl_ok in H7; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          eapply impl_ok in H8; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          eexists.
          intuition; eauto.
          exists s. split.
          exists s. split; eauto.
          constructor.
          constructor.
          eapply td_read1_ok with (state'1 := state'1); eauto.
          rd_trans; auto.
          rd_trans; auto.
          simpl; auto.
          simpl; auto.
        + (* no working disk *)
          rewrite H1 in H11.
          eapply impl_ok in H7; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          eapply impl_ok in H8; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          eexists.
          intuition; eauto.
          exists s. split.
          exists s. split. eauto.
          constructor.
          constructor.
          eapply td_read_none_ok; eauto.
          rd_trans; auto.
          simpl. auto.
          simpl. auto.
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
      inv_exec.
      inv_exec.
      exec_steps.
      inv_rexec.
      inv_rexec.
      eapply RExec in H6.
      eapply impl_ok in H6; eauto. deex.
      exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
      eapply rd_abstraction_failure in H2 as H2'; eauto.
      inv_rexec.
      eapply RExec in H9.
      eapply impl_ok in H9; eauto. deex.
      exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
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
          eapply td_write_d0_ok with (state := state'0) (state''' := state'1) in H6; eauto.
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
      + eapply td_write_failure in H6.
        eapply td_write_failure in H3.
        intuition. subst; simpl in *.
        TD.inv_bg; simpl in *.
        -- unfold rd_abstraction, rd_invariant, abstraction_f in H2'.
          destruct state'1; simpl in *.
          destruct disk0; try congruence.
          destruct disk1; try congruence. intuition.
        -- unfold rd_abstraction, rd_invariant, abstraction_f in H2'.
          intuition.
        -- unfold rd_abstraction, rd_invariant, abstraction_f in H2'.
          intuition. subst.
          destruct pf; auto.
      - simpl in *; auto.
      - simpl in *; auto.
      Unshelve.
      all: eauto; try exact tt; try exact unit.
      all: constructor.
    Admitted.


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

    Lemma td_disk_size_none_ok: forall s state' state'0 state'2 state'1,
      TD.op_step (TD.DiskSize d0) state'0 Failed state' ->
      TD.bg_failure state' state'2  ->
      TD.op_step (TD.DiskSize d1) state'2 Failed state'1 ->
      (@size block s) = 0.
    Proof.
      intros.
      TD.inv_step.
      TD.inv_step.
      simpl in *.
      case_eq (TD.disk1 state'1); intros.
      - rewrite H in H4. inversion H4.
      - rewrite H in H4.
        case_eq (TD.disk0 state'); intros.
        + rewrite H1 in H3. inversion H3.
        + rewrite H1 in H3.
          TD.inv_bg.
          -- apply both_disks_not_missing in H; auto. exfalso. auto.
          -- simpl in *. subst. destruct pf; auto.
          -- simpl in *. subst.
            inversion H1.
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
      inv_exec.
      destruct v0.
      - eapply RExec in H7.
        eapply impl_ok in H7; eauto. deex.
        exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
        TD.inv_step.
        + eapply td_disk_size_ok with (s := s) in H6.
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
        + simpl; auto. 
      - eapply RExec in H7.
        eapply impl_ok in H7; eauto. deex.
        eapply RExec in H9.
        inv_rexec.
        inv_exec.
        destruct v0.
        + eapply RExec in H9.
          eapply impl_ok in H9; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          TD.inv_step.
          eapply td_disk_size_ok with (s := s) in H9.
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
          simpl; auto.
        + eapply RExec in H9.
          eapply impl_ok in H9; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          eexists. split; eauto.
          exists s.
          split; eauto.
          eexists.
          split.
          constructor.
          subst.
          eapply td_disk_size_none_ok with (s := s) in H6 as H6; eauto.
          rewrite <- H6.
          constructor.
          rd_trans. auto.
          simpl; auto.
        + simpl; auto.
      Unshelve.
      all: eauto; try exact unit. 
      constructor.
    Admitted.

    Definition td_disk_size_post (state:TD.State) v :=
      match (TD.get_disk d0 state, TD.get_disk d1 state) with
      | (Some d', Some d'') => size d' = v /\ size d'' = v
      | (Some d', None) => size d' = v
      | (None, Some d'') => size d'' = v
      | (None, None) => False
      end.

    (* The disk is synchronous so at most one address that is out of sync. *)
    Definition recovery_pre (state: TD.State) s a' :=
      a' <= size s ->
      match (TD.get_disk d0 state, TD.get_disk d1 state) with
      | (Some d', Some d'') =>  
        (d' = s /\ d'' = s) \/
        (exists a b, a < a' /\
          ((d' = (diskUpd s a b) /\ d'' = s) \/
           (d' = (diskUpd s a b) /\ d'' = diskUpd s a b)))
      | (Some d', None) => d' = s \/ 
          (exists a b, a < a' /\ d' = diskUpd s a b)
      | (None, Some d'') => d'' = s \/ 
          (exists a b, a < a' /\ d'' = diskUpd s a b)
      | (_, _) => False  (* one disk must be working *)
      end.

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

    Lemma fixup_eq_ok: forall state state'2 state'1 state'0 state' s v b,
      recovery_pre state s (S v) ->
      TD.bg_failure state state'2 ->
      TD.op_step (TD.Read d0 v) state'2 (Working b) state' ->
      TD.bg_failure state' state'1 ->
      TD.op_step (TD.Read d1 v) state'1 (Working b) state'0 ->
      S v < size s ->
      recovery_pre state'0 s v.
    Proof.
      intros.
      TD.inv_step.
      TD.inv_step.
      - unfold recovery_pre in *; intros.
        case_eq (TD.get_disk d0 state'0); intros.
        case_eq (TD.get_disk d1 state'0); intros.
        + rewrite H5 in H9.
          eapply bg_failure_ok in H5; eauto.
          eapply bg_failure_ok in H3; eauto.
          rewrite H3 in H8.
          eapply bg_failure_ok in H5; eauto.
          eapply bg_failure_ok in H3; eauto.
          rewrite H5 in H.
          rewrite H3 in H.
          assert (S v <= size s) by omega.
          specialize (H H6).
          ++ intuition; auto.
            repeat deex.
            destruct (dec_eq_nat a v); subst; simpl in *.
            -- case_eq (d0 v); intros.
              case_eq (d v); intros.
              +++ rewrite H10 in H9; simpl in *.
                rewrite H11 in H8; simpl in *.
                inversion H10. inversion H9; subst.
                intuition; subst; simpl in *.
                left. split; eauto.
                apply diskUpd_same.
                rewrite diskUpd_eq in H11.
                inversion H11; subst; auto.
                inversion H8; subst; auto.
                omega.
                left.
                inversion H9. inversion H8; subst.
                rewrite diskUpd_eq in H11.
                inversion H11; subst; auto.
                (* lost the initial value at s? *)
                admit.
                omega.
              +++ rewrite H11 in H8. deex. 
                intuition.
                subst; simpl in *.
                eapply diskUpd_eq_some with (b := b0) in H10.
                rewrite H11 in H10. inversion H10.
                rewrite H10 in H9. inversion H9. inversion H8; subst.
                rewrite H11 in H10. inversion H10.
              +++ admit.
           --

    Admitted.


    (* fix up for v that isn't out of sync. keep repairing *)
    Lemma fixup_continue_ok: forall v w w' (state: TD.State) s,
      recovery_pre state s (S v) ->
      abstraction (interface_abs td) w state ->
      exec (fixup v) w (Finished Continue w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' s v.
    Proof.
      intros.
      inv_exec.
      destruct v0.
      - eapply RExec in H7.
        eapply impl_ok in H7; eauto. deex.
        inv_exec.
        destruct v1.
        + eapply RExec in H8.
          eapply impl_ok in H8; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          -- rewrite e in H7.
            eapply fixup_eq_ok in H6; eauto.
            admit.
         --
            destruct v2. inversion H5. inversion H5.
         -- simpl; auto.
       + eapply RExec in H8.
         eapply impl_ok in H8; eauto. deex.
         inv_exec.
         inversion H5.
         simpl; auto.
       +
         simpl; auto.
    - eapply RExec in H7.
      eapply impl_ok in H7; eauto. deex.
      inv_exec.
      inversion H3.
    Unshelve.
      all: auto.
    Admitted.


   (* fix up for v that is out of sync, repair and be done *)
   Lemma fixup_repair_ok: forall v w w' (state: TD.State) s,
      recovery_pre state s (S v) ->
      abstraction (interface_abs td) w state ->
      exec (fixup v) w (Finished RepairDone w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' s 0. (* XXX maybe v instead of 0 *)
    Proof.
      intros.
      inv_exec.
      destruct v0.
      - eapply RExec in H7.
        eapply impl_ok in H7; eauto. deex.
        inv_exec.
        destruct v1.
        + eapply RExec in H8.
          eapply impl_ok in H8; eauto. deex.
          destruct (equiv_dec v0 v1).
          -- inv_exec.
            inversion H5.
          -- inv_exec.
            eapply RExec in H10.
            eapply impl_ok in H10; eauto. deex.
   Admitted.

   (* fix up for v that is out of sync, repair and be done *)
   Lemma fixup_repair_failure: forall v w w' (state: TD.State) s i,
      recovery_pre state s (S v) ->
      abstraction (interface_abs td) w state ->
      exec (fixup v) w (Finished (DiskFailed i) w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' s 0.
    Proof.
    Admitted.


    Lemma recover_at_ok: forall v w w' state s,
      recovery_pre state s v ->
      abstraction (interface_abs td) w state ->
      exec (recover_at v) w (Finished RepairDone w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' s 0.
    Proof.
      induction v; intros.
      - exists state.
        inv_exec.
        split; auto.
      - inv_exec.
        destruct v0.
        + eapply fixup_continue_ok with (s := s) in H7 as H7'; eauto.
          deex. 
          specialize (IHv w'0 w' state' s).
          edestruct IHv; eauto.
        + inv_exec.
          eapply fixup_repair_ok with (s := s) in H7 as H7'; eauto.
          (* XXX maybe use induction, if v instead of 0 *)
        + inv_exec.
          eapply fixup_repair_failure with (s := s) in H7 as H7'; eauto.
    Qed.

    Definition td_disk_size_pre (state:TD.State) :=
      match (TD.get_disk d0 state, TD.get_disk d1 state) with
      | (Some d', Some d'') => d' = d'' /\ size d' = size d''
      | (Some d', None) => True
      | (None, Some d'') => True
      | (None, None) => False
      end.

    Lemma recovery_pre_failure: forall state state' s n,
      recovery_pre state n s ->
      TD.bg_failure state state' ->
      recovery_pre state' n s.
    Proof.
      intros.
      TD.inv_bg.
      + auto.
      + unfold recovery_pre in *; simpl in *.
        intuition.
        repeat deex.
        intuition.
        right. exists a, b. split; auto.
      + unfold recovery_pre in *; simpl in *.
        intuition.
        repeat deex.
        intuition.
        - right. exists a, b. split; auto.
        - right. exists a, b. split; auto.
    Qed.


    (* disk size on post-crash, pre-recovery state *)
    Lemma disk_size_ok': forall v w w' state s,
      abstraction (interface_abs td) w state ->
      recovery_pre state s (size s) ->
      exec diskSize w (Finished v w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        td_disk_size_post state' v /\
        recovery_pre state' s (size s).
    Proof.
      intros.
      inv_exec.
      destruct v0.
      - eapply RExec in H7.
        eapply impl_ok in H7; eauto. deex.
        exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
        TD.inv_step; simpl in *.
        + eapply recovery_pre_failure in H2; eauto. 
          exists state'.
          split; auto.
          split; auto.
          case_eq (TD.disk0 state'); intros.
          -- rewrite H3 in H6; simpl in *.
            inversion H6.
            unfold td_disk_size_post.
            unfold recovery_pre in H2; simpl in *.
            rewrite H3 in *; simpl in *.
            case_eq (TD.disk1 state'); intros; auto.
            ++  rewrite H4 in *; simpl in *.
              intuition; subst; auto.
              repeat deex.
              intuition; subst; auto.
              destruct H2; intuition; subst; auto.
              repeat deex.
              intuition; subst; auto.
              rewrite diskUpd_size; auto.
          -- rewrite H3 in H6; simpl in *.
            inversion H6; auto.
        + simpl; auto.
      - inv_exec.
        destruct v0.
        + inv_exec.
          eapply RExec in H7.
          eapply impl_ok in H7; eauto. deex.
          eapply RExec in H6.
          eapply impl_ok in H6; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          TD.inv_step.
          TD.inv_step.
          simpl in *.
          case_eq (TD.disk0 state'); intros.
          -- rewrite H5 in H8. inversion H8.
          -- rewrite H5 in H8.
             case_eq (TD.disk1 state'0); intros.
             ++ rewrite H6 in H9.
              inversion H9.
              eapply bg_failure_disk_none with (id := d0) in H5 as H5'; eauto.
              exists state'0.
              split; auto.
              eapply recovery_pre_failure in H2; eauto.
              eapply recovery_pre_failure in H4; eauto.
              split; auto.
              unfold td_disk_size_post. subst; simpl.
              rewrite H6; simpl in *.
              rewrite H5'; simpl; auto.
            ++ 
              eapply bg_failure_disk_none with (id := d0) in H4 as H4'; simpl in *.
              apply both_disks_not_missing in H6; eauto.
              exfalso; auto. auto.
         -- simpl; auto.
         -- simpl; auto.
        + inv_exec.
          eapply RExec in H7.
          eapply impl_ok in H7; eauto. deex.
          eapply RExec in H6.
          eapply impl_ok in H6; eauto. deex.
          exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          TD.inv_step.
          TD.inv_step.
          simpl in *.
          case_eq (TD.disk1 state'0); intros; rewrite H5 in *.
          -- inversion H9.
          -- case_eq (TD.disk0 state'); intros; rewrite H6 in *.
             ++ inversion H8.
             ++ eapply bg_failure_disk_none with (id := d0) in H4 as H4'; simpl in *; auto.
              apply both_disks_not_missing in H5; eauto.
              exfalso; auto.
          -- simpl; auto.
          -- simpl; auto.
      Unshelve.
      all: eauto; try exact unit.
    Qed.

    Lemma recover_finish_ok: forall w w' s state,
      abstraction (interface_abs td) w state ->
      recovery_pre state s (size s) ->
      exec Recover w (Finished tt w') ->
      exists state',
        abstraction (interface_abs td) w' state' /\
        recovery_pre state' s 0.
    Proof.
      intros.
      inv_exec.
      inv_exec.
      destruct v0.
      - admit.
      - eapply disk_size_ok' with (state := state) in H7; eauto.
        deex.
        eapply recover_at_ok with (state := state') in H6; eauto.
        (* XXX why is v (size s) omega *) 
        admit.
      - eapply disk_size_ok' with (state := state) in H7; eauto.
        deex.
        assert (TD.get_disk i state' = None).
        admit.
    Admitted.

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
      recovery_pre state s (size s).
    Proof.
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
    Qed.


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


    (* write with crash *)
    Lemma write_crash_ok: forall a b w w' state s,
      abstraction (interface_abs td) w state ->
      rd_abstraction state s -> 
      exec (write a b) w (Crashed w') ->
      exists state',
       abstraction (interface_abs td) w' state' /\ recovery_pre state' s (size s).
    Proof.
      intros.
      inv_exec.
      - exists state.
        split; auto.
        apply rd_abstraction_recovery_pre; auto.
      - eapply RExec in H7.
        eapply impl_ok in H7; eauto. deex.
        inv_exec.
        + exec_steps; repeat ( ReplicatedDisk.inv_bg || ReplicatedDisk.inv_step ).
          exists state'.
          split; auto.
          apply rd_abstraction_failure with (s:=s) in H2; auto.
          eapply write0_crash_ok with (state := state'0); eauto.
        + eapply RExec in H8.
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

    Lemma write_recover_ok: forall s a b w state w' w'' w''',
      abstraction (interface_abs td) w state ->
      rd_abstraction state s ->
      exec (write a b) w (Crashed w') ->
      exec (irec td) (world_crash w') (Finished tt w'') ->
      exec Recover w'' (Finished tt w''') ->
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
          unfold prog_spec; intros.
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
          unfold prog_spec; intros.
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
          unfold prog_spec; intros.
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
