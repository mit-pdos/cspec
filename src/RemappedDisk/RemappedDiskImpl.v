Require Import POCS.
Require Import OneDisk.OneDiskAPI.
Require Import BadSectorDisk.BadSectorAPI.


Module RemappedDisk (bd : BadSectorAPI) <: OneDiskAPI.

  Definition read (a : addr) : prog block :=
    bs <- bd.getBadSector;
    if a == bs then
      len <- bd.diskSize;
      r <- bd.read (len-1);
      Ret r
    else
      r <- bd.read a;
      Ret r.

  Definition write (a : addr) (b : block) : prog unit :=
    len <- bd.diskSize;
    if a == (len-1) then
      Ret tt
    else
      bs <- bd.getBadSector;
      if a == bs then
        _ <- bd.write (len-1) b;
        Ret tt
      else
        _ <- bd.write a b;
        Ret tt.

  Definition diskSize : prog nat :=
    len <- bd.diskSize;
    Ret (len - 1).

  Definition init : prog InitResult :=
    len <- bd.diskSize;
    if len == 0 then
      Ret InitFailed
    else
      bs <- bd.getBadSector;
      if (lt_dec bs len) then
        Ret Initialized
      else
        Ret InitFailed.

  Definition recover : prog unit :=
    bd.recover.


  Inductive remapped_abstraction (bs_state : BadSectorAPI.State) (rd_disk : OneDiskAPI.State) : Prop :=
    | RemappedAbstraction :
      let bs_disk := stateDisk bs_state in
      let bs_addr := stateBadSector bs_state in
      forall
        (* Fill in the rest of your abstraction here. *)
        (* Hint 1: What should be true about the non-bad sectors? *)
        (* Hint 2: What should be true about the bad sector? *)
        (* Hint 3: What if the bad sector address is the last address? *)
        (* Hint 4: What if the bad sector address is past the end of the disk? *)
        (* SOL *)
        (Hgoodsec : forall a, a <> bs_addr /\ a <> size rd_disk -> bs_disk a = rd_disk a)
        (Hremap : bs_addr <> size rd_disk -> bs_disk (size rd_disk) = rd_disk bs_addr)
        (Hbsok : bs_addr < size bs_disk)
        (* END *)
        (Hsize : size bs_disk = size rd_disk + 1),
      remapped_abstraction bs_state rd_disk.

  Definition abstr : Abstraction OneDiskAPI.State :=
    abstraction_compose bd.abstr {| abstraction := remapped_abstraction |}.

  Ltac invert_abstraction :=
    match goal with
    | H : remapped_abstraction _ _ |- _ => inversion H; clear H; subst_var; simpl in *
    end.


  Theorem read_ok : forall a, prog_spec (OneDiskAPI.read_spec a) (read a) recover abstr.
  Proof.
    unfold read.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.
    2: unfold wipe in *; simpl in *; intuition subst; eauto.

    destruct (a == r); subst.
    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      exists s. split. split. auto.
      2: auto.

      invert_abstraction.
      rewrite Hsize in H7.
      replace (size s + 1 - 1) with (size s) in * by omega.

      destruct (stateBadSector state == size s).
      + rewrite disk_oob_eq by omega. constructor.
      + rewrite <- Hremap; auto.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      exists s. split. split. auto.
      2: auto.

      invert_abstraction.

      destruct (a == size s).
      + rewrite disk_oob_eq by omega. constructor.
      + rewrite <- Hgoodsec; auto.
  Qed.

  Lemma remapped_abstraction_diskUpd_remap : forall state s v,
    remapped_abstraction state s ->
    remapped_abstraction (mkState
      (diskUpd (stateDisk state) (size (stateDisk state) - 1) v)
      (stateBadSector state)) (diskUpd s (stateBadSector state) v).
  Proof.
    intros.
    invert_abstraction.
    rewrite Hsize. replace (size s + 1 - 1) with (size s) by omega.
    constructor; simpl.

    all: autorewrite with upd; intuition idtac.
    repeat rewrite diskUpd_neq by omega. eauto.
    repeat rewrite diskUpd_eq by omega; auto.
  Qed.

  Lemma remapped_abstraction_diskUpd_noremap : forall state s a v,
    remapped_abstraction state s ->
    a <> size (stateDisk state) - 1 ->
    a <> stateBadSector state ->
    remapped_abstraction (mkState
      (diskUpd (stateDisk state) a v)
      (stateBadSector state)) (diskUpd s a v).
  Proof.
    intros.
    invert_abstraction.
    constructor; simpl.

    all: autorewrite with upd; intuition idtac.

    destruct (lt_dec a (size s)).
    destruct (a == a0); subst.
    repeat rewrite diskUpd_eq by omega; auto.
    repeat rewrite diskUpd_neq by omega; auto.
    repeat rewrite diskUpd_oob_noop by omega. auto.

    repeat rewrite diskUpd_neq by omega. eauto.
  Qed.

  Hint Resolve remapped_abstraction_diskUpd_remap.
  Hint Resolve remapped_abstraction_diskUpd_noremap.

  Theorem write_ok : forall a v, prog_spec (OneDiskAPI.write_spec a v) (write a v) recover abstr.
  Proof.
    unfold write.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.
    2: unfold wipe in *; simpl in *; intuition subst; eauto.

    destruct (a == r-1); subst.
    - step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      exists s. split. split. auto.
      2: auto.

      rewrite diskUpd_oob_noop; auto.
      invert_abstraction.
      omega.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: unfold wipe in *; simpl in *; intuition subst; eauto.

      destruct (a == r0).
      + step_prog; intros.
        exists tt; simpl; intuition idtac.
        2: unfold wipe in *; simpl in *; intuition subst; eauto.
        2: unfold wipe in *; simpl in *; intuition subst; eauto.

        step_prog; intros.
        eauto.

        simpl in *; intuition subst.
        2: unfold wipe in *; simpl in *; intuition subst; eauto.

        eauto.

      + step_prog; intros.
        exists tt; simpl; intuition idtac.
        2: unfold wipe in *; simpl in *; intuition subst; eauto.
        2: unfold wipe in *; simpl in *; intuition subst; eauto.

        step_prog; intros.
        eauto.

        simpl in *; intuition subst.
        2: unfold wipe in *; simpl in *; intuition subst; eauto.
        eauto.
  Qed.

  Theorem diskSize_ok : prog_spec OneDiskAPI.diskSize_spec diskSize recover abstr.
  Proof.
    unfold diskSize.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.
    2: unfold wipe in *; simpl in *; intuition subst; eauto.

    step_prog; intros.
    eauto.

    simpl in *; intuition subst.
    2: unfold wipe in *; simpl in *; intuition subst; eauto.

    exists s. split. split. auto.
    2: auto.

    invert_abstraction.
    omega.
  Qed.

  Theorem recover_noop : rec_noop recover abstr OneDiskAPI.wipe.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_prog; intros.
    eauto.

    destruct a; simpl in *.
    unfold wipe, OneDiskAPI.wipe in *; intuition eauto.
    subst; eauto.
  Qed.

End RemappedDisk.


Require Import BadSectorImpl.
Module x := RemappedDisk BadSectorDisk.
Print Assumptions x.write_ok.
