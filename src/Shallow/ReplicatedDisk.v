Require Import Disk.
Require Import Automation.

Require Import Shallow.ProgLang.Prog.
Require Import Shallow.ProgLang.Hoare.
Require Import Shallow.TwoDiskAPI.
Require Import Shallow.SeqDiskAPI.

Require Import Shallow.ReplicatedDisk.Step.
Require Import Shallow.ReplicatedDisk.DiskSize.
Require Import Shallow.ReplicatedDisk.Recovery.
Require Import Shallow.ReplicatedDisk.ReadWrite.

Require Import MaybeHolds.
Require Import Shallow.Interface.

Module RD.

  Section ReplicatedDisk.

    Variable (td:Interface TD.API).

    Theorem Read_rok : forall a,
        prog_rspec
          (fun d state =>
             {|
               pre := TD.disk0 state |= eq d /\
                      TD.disk1 state |= eq d;
               post :=
                 fun r state' =>
                   d a |= eq r /\
                   TD.disk0 state' |= eq d /\
                   TD.disk1 state' |= eq d;
               recover :=
                 fun _ state' =>
                   TD.disk0 state' |= eq d /\
                   TD.disk1 state' |= eq d;
             |})
          (Read td a) (_ <- irec td; Recover td)
          (refinement td).
    Proof.
      intros.
      eapply compose_recovery.
      eapply Read_ok.
      eapply Recover_ok.
      simplify.
      rename a0 into d.
      descend; intuition eauto.
      simplify.
      exists d, FullySynced; intuition eauto.
    Qed.

    Theorem Write_rok : forall a b,
        prog_rspec
          (fun d state =>
             {|
               pre :=
                 TD.disk0 state |= eq d /\
                 TD.disk1 state |= eq d;
               post :=
                 fun r state' =>
                   r = tt /\
                   TD.disk0 state' |= eq (diskUpd d a b) /\
                   TD.disk1 state' |= eq (diskUpd d a b);
               recover :=
                 fun _ state' =>
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq (diskUpd d a b));
             |})
          (Write td a b) (_ <- irec td; Recover td)
          (refinement td).
    Proof.
      intros.
      eapply compose_recovery.
      eapply Write_ok.
      eapply Recover_ok.
      simplify.
      rename a0 into d.
      descend; (intuition eauto); simplify.
      exists d, FullySynced; intuition eauto.
      exists d, (OutOfSync a b); intuition eauto.
      exists (diskUpd d a b), FullySynced; intuition eauto.
    Qed.

    Theorem DiskSize_rok :
      prog_rspec
        (fun d state =>
           {|
             pre := TD.disk0 state |= eq d /\
                    TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                 r = size d /\
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
             recover :=
               fun _ state' =>
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
           |})
        (DiskSize td) (_ <- irec td; Recover td)
        (refinement td).
    Proof.
      eapply compose_recovery.
      eapply prog_rok_to_rspec; [ eapply DiskSize_ok | eauto | simplify ].
      eapply Recover_ok.
      simplify.

      rename a into d.
      exists d, FullySynced; intuition eauto.
      simplify.
      exists d, FullySynced; intuition eauto.
    Qed.

    Lemma read_step : forall a (state state':D.State) b,
        state a |= eq b ->
        state' = state ->
        D.step (D.Read a) state b state'.
    Proof.
      intros; subst.
      constructor; auto.
      intros.
      replace (state a) in *; auto.
    Qed.

    Lemma write_step : forall a b (state state':D.State) u,
        state' = diskUpd state a b ->
        D.step (D.Write a b) state u state'.
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

    Hint Resolve read_step write_step disk_size_step.

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

    Hint Resolve tt.

    Lemma invariant_to_disks_eq : forall state,
        rd_invariant state ->
        TD.disk0 state |= eq (rd_abstraction state) /\
        TD.disk1 state |= eq (rd_abstraction state).
    Proof.
      destruct state; simpl; intros.
      destruct matches in *; eauto.
    Qed.

    Lemma disks_eq_to_invariant : forall state d,
        TD.disk0 state |= eq d ->
        TD.disk1 state |= eq d ->
        rd_invariant state.
    Proof.
      destruct state; simpl; intros.
      destruct matches in *; eauto.
    Qed.

    Lemma disks_eq_to_abstraction : forall state d,
        TD.disk0 state |= eq d ->
        TD.disk1 state |= eq d ->
        rd_abstraction state = d.
    Proof.
      destruct state; simpl; intros.
      destruct matches in *; eauto.
      exfalso; eauto.
    Qed.

    Hint Extern 1 (TD.disk0 _ |= eq (rd_abstraction _)) => apply invariant_to_disks_eq.
    Hint Extern 1 (TD.disk1 _ |= eq (rd_abstraction _)) => apply invariant_to_disks_eq.
    Hint Resolve disks_eq_to_invariant disks_eq_to_abstraction.

    Definition d_op_impl T (op:D.Op T) : prog T :=
      match op with
      | D.Read a => Read td a
      | D.Write a b => Write td a b
      | D.DiskSize => DiskSize td
      end.

    Definition rd_refinement :=
      refinement_compose
        (refinement td)
        {| invariant := rd_invariant;
           abstraction := rd_abstraction; |}.

    Definition impl : InterfaceImpl D.Op :=
      {| op_impl := d_op_impl;
         recover_impl := _ <- irec td; Recover td; |}.

    Definition rd : Interface D.API.
      unshelve econstructor.
      - exact impl.
      - exact rd_refinement.
      - intros.
        destruct op; unfold op_spec; simpl.
        + apply rspec_refinement_compose; simpl.
          eapply prog_rspec_weaken; [ apply Read_rok | ].
          unfold rspec_impl; simplify.
          exists (rd_abstraction state); (intuition eauto); simplify.
        + apply rspec_refinement_compose; simpl.
          eapply prog_rspec_weaken; [ apply Write_rok | ].
          unfold rspec_impl; simplify.
          exists (rd_abstraction state); (intuition eauto); simplify.
        + apply rspec_refinement_compose; simpl.
          eapply prog_rspec_weaken; [ apply DiskSize_rok | ].
          unfold rspec_impl; simplify.
          exists (rd_abstraction state); (intuition eauto); simplify.
      - eapply rec_noop_compose; eauto; simpl.
        eapply prog_rspec_weaken; [ eapply Recover_rok | ].
        unfold rspec_impl; simplify.
        exists (rd_abstraction state), FullySynced; intuition eauto.

        Grab Existential Variables.
        all: auto.
    Defined.

    Definition prim T (op: D.Op T) : prog T :=
      Prim rd op.

    Definition recover : prog unit :=
      irec rd.

  End ReplicatedDisk.

End RD.
