Require Import Automation.
Require Import Disk.SimpleDisk.
Require Import Omega.

Require Import RemappedDisk.RemappedDiskAPI.
Require Import BadSectorDisk.BadSectorAPI.
Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import Refinement.ProgLang.NoCrashes.

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
      len <- Prim bd (BadSectorDisk.DiskSize);
      if a == (len-1) then
        Ret tt
      else
        bs <- Prim bd (BadSectorDisk.GetBadSector);
        if a == bs then
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

    Definition init : prog InitResult :=
      len <- Prim bd (BadSectorDisk.DiskSize);
      if len == 0 then
        Ret InitFailed
      else
        bs <- Prim bd (BadSectorDisk.GetBadSector);
        if (lt_dec bs len) then
          Ret Initialized
        else
          Ret InitFailed.

    Definition impl : InterfaceImpl RemappedDisk.Op :=
      {| op_impl := rd_op_impl;
         recover_impl := Ret tt;
         init_impl := then_init (iInit bd) init; |}.

    Definition remapped_abstraction (bs_state : BadSectorDisk.State) (rd_disk : RemappedDisk.State) :=
      let '(BadSectorDisk.mkState bs_disk bs_addr) := bs_state in
      size bs_disk = size rd_disk + 1 /\
      (forall a, a <> bs_addr /\ a <> size rd_disk -> bs_disk a = rd_disk a) /\
      (bs_addr <> size rd_disk -> bs_disk (size rd_disk) = rd_disk bs_addr) /\
      bs_addr < size bs_disk.

    Definition abstr : Abstraction RemappedDisk.State :=
      abstraction_compose
        (interface_abs bd)
        {| abstraction := remapped_abstraction |}.

    Definition rd : Interface RemappedDisk.API.
      unshelve econstructor.
      - exact impl.
      - exact abstr.
      - intros.
        destruct op; unfold op_spec;
          apply spec_abstraction_compose;
            unfold spec_impl, remapped_abstraction.
        + unfold prog_spec; intros.
          destruct a0; simpl in *; intuition.
          destruct state.
          inv_rexec; try cannot_crash.
          exec_steps; repeat ( BadSectorDisk.inv_bg || BadSectorDisk.inv_step ).

          * eexists; intuition. eauto. simpl.
            exists s. intuition.
            eexists; intuition. reflexivity. constructor.
            rewrite <- H11. rewrite e0.
            replace (size s + 1 - 1) with (size s) by omega.
            destruct (v0 == size s).
           -- right.
              apply disk_oob_eq.
              rewrite e. rewrite e3. omega.
           -- left.
              rewrite e2; eauto.

          * exfalso.
            eapply disk_inbounds_not_none.
            2: eauto.
            omega.

          * eexists; intuition. eauto. simpl.
            exists s. intuition.
            eexists; intuition. reflexivity. constructor. right.
            apply disk_oob_eq.
            rewrite e. rewrite e0. omega.

          * eexists; intuition. eauto. simpl.
            exists s. intuition.
            eexists; intuition. reflexivity. constructor.
            rewrite <- H8.
            destruct (a == size s).
           -- right.
              apply disk_oob_eq.
              rewrite e2. omega.
           -- left.
              rewrite e0; eauto.

          * eexists; intuition. eauto. simpl.
            exists s. intuition.
            eexists; intuition. reflexivity. constructor. right.
            apply disk_oob_eq.
            apply disk_none_oob in H8. omega.

          * congruence.

        + unfold prog_spec; intros.
          destruct a0; simpl in *; intuition.
          destruct state.
          inv_rexec; try cannot_crash.
          exec_steps; repeat ( BadSectorDisk.inv_bg || BadSectorDisk.inv_step ).

          * eexists; intuition. eauto. simpl.
            exists s. intuition.
            eexists; intuition. reflexivity.
            replace s with (diskUpd s a b) at 2. constructor.
            apply diskUpd_none. apply disk_oob_eq. rewrite e. omega.

          * eexists; intuition. eauto. simpl.
            exists (diskUpd s a b). intuition.
            eexists; intuition. reflexivity. constructor.

           -- repeat rewrite diskUpd_size; omega.

           -- rewrite diskUpd_size in *. rewrite e2.
              rewrite e. replace (size s + 1 - 1) with (size s) by omega.
              repeat rewrite diskUpd_neq by congruence. eauto.

           -- rewrite e in *. replace (size s + 1 - 1) with (size s) in * by omega.
              rewrite diskUpd_size. rewrite diskUpd_eq by omega.
              rewrite e2 in *. rewrite diskUpd_eq; auto.
              destruct (eq_nat_dec v1 (size s)); try congruence. omega.

           -- rewrite diskUpd_size. eauto.

          * eexists; intuition. eauto. simpl.
            exists (diskUpd s a b). intuition.
            eexists; intuition. reflexivity. constructor.

           -- repeat rewrite diskUpd_size; omega.

           -- rewrite e in *. replace (size s + 1 - 1) with (size s) in * by omega.
              destruct (a == a0).
             ++ rewrite e2 in *.
                destruct (lt_dec a0 (size d)).
               ** rewrite diskUpd_eq by auto.
                  rewrite diskUpd_eq; auto.
                  destruct (eq_nat_dec a0 (size s)); try congruence. omega.
               ** rewrite diskUpd_oob_eq by auto.
                  rewrite diskUpd_oob_eq by omega. auto.
             ++ repeat rewrite diskUpd_neq by congruence.
                rewrite diskUpd_size in *. auto.

           -- rewrite e in *. replace (size s + 1 - 1) with (size s) in * by omega.
              rewrite diskUpd_size in *.
              repeat rewrite diskUpd_neq by congruence.
              eauto.

           -- rewrite diskUpd_size. eauto.

        + unfold prog_spec; intros.
          destruct a; simpl in *; intuition.
          destruct state.
          inv_rexec; try cannot_crash.
          exec_steps; repeat ( BadSectorDisk.inv_bg || BadSectorDisk.inv_step ).

          eexists; intuition. eauto. simpl.
          exists s. intuition.
          eexists; intuition. reflexivity.

          rewrite H3.
          replace (size s + 1 - 1) with (size s) in * by omega.
          constructor.

      - cannot_crash.
      - eapply then_init_compose; eauto.

        unfold prog_spec; intros.
        destruct a; simpl in *; intuition.
        destruct state.
        inv_rexec; try cannot_crash.
        exec_steps; repeat ( BadSectorDisk.inv_bg || BadSectorDisk.inv_step ).

        + eexists; intuition; eauto.

        + eexists; intuition; eauto; simpl.
          case_eq (d (size d - 1)); intros.

          * exists (diskUpd (shrink d) v1 b).
            rewrite diskUpd_size in *.
            intuition.

           -- apply shrink_size. congruence.
           -- rewrite diskUpd_neq by congruence.
              apply shrink_preserves. congruence.
           -- rewrite shrink_size in * by congruence.
              rewrite diskUpd_eq.
              replace (size (shrink d) + 1 - 1) with (size (shrink d)) in * by omega.
              auto.

              (* why is [omega] too weak here? *)
              inversion l; try omega.
              exfalso. apply H4.
              replace (size (shrink d) + 1) with (S (size (shrink d))) in H6 by omega.
              congruence.

          * apply disk_none_oob in H2. omega.

        + eexists; intuition; eauto.

      Unshelve.
      all: eauto.

    Defined.

  End Implementation.

End RemappedDisk.
