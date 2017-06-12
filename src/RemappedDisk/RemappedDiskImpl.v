Require Import Automation.
Require Import Disk.SimpleDisk.
Require Import Omega.

Require Import RemappedDisk.RemappedDiskAPI.
Require Import BadSectorDisk.BadSectorAPI.
Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.

Module RemappedDisk.

  Section Implementation.

    Variable (bd : Interface BadSectorDisk.API).

    Definition read (a : addr) : prog block :=
      bs <- Prim bd (BadSectorDisk.GetBadSector);
      if a == bs then
        len <- Prim bd (BadSectorDisk.DiskSize);
        Prim bd (BadSectorDisk.Read (len-1))
      else
        Prim bd (BadSectorDisk.Read a).

    Definition write (a : addr) (b : block) : prog unit :=
      bs <- Prim bd (BadSectorDisk.GetBadSector);
      if a == bs then
        len <- Prim bd (BadSectorDisk.DiskSize);
        Prim bd (BadSectorDisk.Write (len-1) b)
      else
        Prim bd (BadSectorDisk.Write a b).

    Definition diskSize : prog nat :=
      len <- Prim bd (BadSectorDisk.DiskSize);
      Ret (len - 1).

    Definition rd_op_impl T (op: RemappedDisk.Op T) : prog T :=
      match op with
      | RemappedDisk.Read a => read a
      | RemappedDisk.Write a b => write a b
      | RemappedDisk.DiskSize => diskSize
      end.

    Definition impl : InterfaceImpl RemappedDisk.Op :=
      {| op_impl := rd_op_impl;
         recover_impl := Ret tt;
         init_impl := Ret Initialized; |}.

    Definition remapped_abstraction (bs_state : BadSectorDisk.State) (rd_disk : RemappedDisk.State) :=
      let '(BadSectorDisk.mkState bs_disk bs_addr) := bs_state in
      size bs_disk = size rd_disk + 1 /\
      bs_disk (size rd_disk) = rd_disk bs_addr /\
      forall a, a <> bs_addr /\ a <> size rd_disk ->
      bs_disk a = rd_disk a.

    Definition refinement : Refinement RemappedDisk.State :=
      refinement_compose
        (refinement bd)
        {| abstraction := remapped_abstraction |}.

    Definition rd : Interface RemappedDisk.API.
      unshelve econstructor.
      - exact impl.
      - exact refinement.
      - intros.
        destruct op; unfold op_spec;
          apply spec_refinement_compose;
            unfold spec_impl, remapped_abstraction.
        + unfold prog_spec; intros.
          destruct a0; simpl in *; intuition.
          destruct state.
          inv_rexec.
          * repeat ( match goal with
            | H: exec (Prim _ _) _ _ |- _ => eapply RExec in H
            | H: exec (if ?cond then _ else _) _ _ |- _ => destruct cond
            | H: rexec _ _ _ _ |- _ => eapply impl_ok in H; eauto; deex
            end || inv_ret || inv_exec ).

           -- simpl in *.
              unfold pre_step in *; repeat deex.
              repeat BadSectorDisk.inv_bg.
              repeat BadSectorDisk.inv_step.

              intuition.

              {
                eexists; intuition. eauto. simpl.
                exists s. intuition.
                eexists; intuition. reflexivity. constructor. left.
                rewrite <- H1. rewrite e0.
                replace (size s + 1 - 1) with (size s) by omega.
                congruence.
              }

              {
                exfalso.
                eapply disk_inbounds_not_none.
                2: eauto.
                omega.
              }

              {
                eexists; intuition. eauto. simpl.
                exists s. intuition.
                eexists; intuition. reflexivity. constructor. right.
                eapply disk_oob_eq. replace a with v0 by congruence.
                omega.
              }

           -- simpl in *.
              unfold pre_step in *; repeat deex.
              repeat BadSectorDisk.inv_bg.
              repeat BadSectorDisk.inv_step.

              intuition.

              eexists; intuition. eauto. simpl.
              exists s. intuition.
              eexists; intuition. reflexivity. constructor.
              case_eq (s a); intros.
              left.
              rewrite <- H1. rewrite e1; auto. split; eauto.
              intro; subst.
              rewrite disk_oob_eq in H4; try congruence. omega.
              right; eauto.

              eexists; intuition. eauto. simpl.
              exists s. intuition.
              eexists; intuition. reflexivity. constructor.
              right. rewrite <- e1; eauto.
              split; eauto.
              intro; subst.
              apply disk_inbounds_not_none in H4; eauto. omega.

          * admit.

        + unfold prog_spec; intros.
          destruct a0; simpl in *; intuition.
          destruct state.
          inv_rexec.
          * repeat ( match goal with
            | H: exec (Prim _ _) _ _ |- _ => eapply RExec in H
            | H: exec (if ?cond then _ else _) _ _ |- _ => destruct cond
            | H: rexec _ _ _ _ |- _ => eapply impl_ok in H; eauto; deex
            end || inv_ret || inv_exec ).

           -- replace a with v0 in * by congruence.

              simpl in *.
              unfold pre_step in *; repeat deex.
              repeat BadSectorDisk.inv_bg.
              repeat BadSectorDisk.inv_step.

              intuition.

              eexists; intuition. eauto. simpl.

              exists (diskUpd s v0 b).
              destruct (lt_dec v0 (size s)).

              {
                intuition.
                eexists; intuition. reflexivity. econstructor. eauto.

                repeat rewrite diskUpd_size. eauto.

                rewrite diskUpd_size.
                rewrite e0.
                replace (size s + 1 - 1) with (size s) by omega.
                rewrite diskUpd_eq by omega.
                rewrite diskUpd_eq; eauto.

(* XXX *)


                rewrite diskUpd_neq with (a := v0) by auto.
                rewrite <- e2.
                rewrite diskUpd_neq; auto.

              

              rewrite H0 in H13. replace (size s + 1 - 1) with (size s) in H13 by omega.
              congruence.

           -- simpl in *.
              unfold pre_step in *; repeat deex.
              repeat BadSectorDisk.inv_bg.
              repeat BadSectorDisk.inv_step.

              eexists; intuition. eauto. simpl.

              exists s. intuition.
              eexists; intuition. reflexivity. constructor.
              rewrite H5 in H10 by assumption. eauto.


      - unfold rec_noop; simpl; intros.
        unfold prog_spec; simpl; intros.
        inv_rexec; inv_ret; eauto.
        admit.
      - apply init_ok.
    Admitted.

  End Implementation.

End BadSectorDisk.
