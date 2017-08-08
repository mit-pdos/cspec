Require Import POCS.
Require Import OneDiskAPI.
Require Import BadSectorAPI.


Module RemappedDisk (bd : BadSectorAPI) <: OneDiskAPI.

  Definition read (a : addr) : prog block :=
    bs <- bd.getBadSector;
    if a == bs then
      len <- bd.size;
      r <- bd.read (len-1);
      Ret r
    else
      r <- bd.read a;
      Ret r.

  Definition write (a : addr) (b : block) : prog unit :=
    len <- bd.size;
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

  Definition size : prog nat :=
    len <- bd.size;
    Ret (len - 1).

  Definition init' : prog InitResult :=
    len <- bd.size;
    if len == 0 then
      Ret InitFailed
    else
      bs <- bd.getBadSector;
      if (lt_dec bs len) then
        Ret Initialized
      else
        Ret InitFailed.

  Definition init := then_init bd.init init'.

  Definition recover : prog unit :=
    bd.recover.


  Inductive remapped_abstraction (bs_state : BadSectorAPI.State) (rd_disk : OneDiskAPI.State) : Prop :=
    | RemappedAbstraction :
      let bs_disk := stateDisk bs_state in
      let bs_addr := stateBadSector bs_state in
      forall
        (* Fill in the rest of your abstraction here. *)
        (* Hint 0: Try to prove [Read]'s correctness to discover what you need from this abstraction *)
        (* Hint 1: What should be true about the non-bad sectors?   Replace [True] with what needs to be true *)
        (Hgoodsectors : True)
        (* Hint 2: What should be true about the bad sector? *)
        (Hbadsector : True)
        (* Hint 3: What if the bad sector address is the last address? *)
        (Hbadlast : True)
        (* Hint 4: What if the bad sector address is past the end of the disk? *)
        (* Hint 5: To refer to the contents of disk [d] at address [a], you can write [d a] *)
        (* Hint 6: To refer to the size of disk [d], you can write [size d] *)
        (* SOL *)
        (Hgoodsec : forall a, a <> bs_addr /\ a <> diskSize rd_disk -> diskGet bs_disk a = diskGet rd_disk a)
        (Hremap : bs_addr <> diskSize rd_disk -> diskGet bs_disk (diskSize rd_disk) = diskGet rd_disk bs_addr)
        (Hbsok : bs_addr < diskSize bs_disk)
        (* END *)
        (Hsize : diskSize bs_disk = diskSize rd_disk + 1),
      remapped_abstraction bs_state rd_disk.

  Definition abstr : Abstraction OneDiskAPI.State :=
    abstraction_compose bd.abstr {| abstraction := remapped_abstraction |}.

  Ltac invert_abstraction :=
    match goal with
    | H : remapped_abstraction _ _ |- _ => inversion H; clear H; subst_var; simpl in *
    end.


  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.

    step_prog; intros.
    exists tt; simpl; intuition idtac.

    destruct (r == 0).
    step_prog; intros; eauto.

    step_prog; intros.
    exists tt; simpl; intuition idtac.

    destruct (lt_dec r0 r).
    all: step_prog; intros; eauto.

    simpl in *; intuition subst.

    case_eq (diskGet (stateDisk state) (diskSize (stateDisk state) - 1)); intros.
    2: exfalso; eapply disk_inbounds_not_none; [ | eauto ]; omega.

    exists (diskUpd (shrink (stateDisk state)) (stateBadSector state) b).
    unfold inited_any. (intuition idtac); auto; intros; autorewrite with upd in *; intuition idtac.
    rewrite diskUpd_neq by omega.
    rewrite shrink_preserves; auto.
    rewrite shrink_size; omega.

    rewrite diskUpd_eq; auto.
    rewrite shrink_size; omega.
    omega.
  Qed.

  Theorem read_ok : forall a, prog_spec (OneDiskAPI.read_spec a) (read a) recover abstr.
  Proof.
    unfold read.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.
    2: autounfold in *; simpl in *; intuition subst; eauto.

    destruct (a == r).
    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      exists s. split. split. auto.
      2: auto.

      invert_abstraction.
      rewrite Hsize in H7.
      replace (diskSize s + 1 - 1) with (diskSize s) in * by omega.

      destruct (stateBadSector state == diskSize s).
      + rewrite disk_oob_eq by omega. constructor.
      + rewrite <- Hremap; auto.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      exists s. split. split. auto.
      2: auto.

      invert_abstraction.

      destruct (a == diskSize s).
      + rewrite disk_oob_eq by omega. constructor.
      + rewrite <- Hgoodsec; auto.
  Qed.

  Lemma remapped_abstraction_diskUpd_remap : forall state s v,
    remapped_abstraction state s ->
    remapped_abstraction (mkState
      (diskUpd (stateDisk state) (diskSize (stateDisk state) - 1) v)
      (stateBadSector state)) (diskUpd s (stateBadSector state) v).
  Proof.
    intros.
    invert_abstraction.
    rewrite Hsize. replace (diskSize s + 1 - 1) with (diskSize s) by omega.
    constructor; simpl.

    all: autorewrite with upd; intuition idtac.
    repeat rewrite diskUpd_neq by omega. eauto.
    repeat rewrite diskUpd_eq by omega; auto.
  Qed.

  Lemma remapped_abstraction_diskUpd_noremap : forall state s a v,
    remapped_abstraction state s ->
    a <> diskSize (stateDisk state) - 1 ->
    a <> stateBadSector state ->
    remapped_abstraction (mkState
      (diskUpd (stateDisk state) a v)
      (stateBadSector state)) (diskUpd s a v).
  Proof.
    intros.
    invert_abstraction.
    constructor; simpl.

    all: autorewrite with upd; intuition idtac.

    destruct (lt_dec a (diskSize s)).
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
    2: autounfold in *; simpl in *; intuition subst; eauto.

    destruct (a == r-1); subst.
    - step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      exists s. split. split. auto.
      2: auto.

      rewrite diskUpd_oob_noop; auto.
      invert_abstraction.
      omega.

    - step_prog; intros.
      exists tt; simpl; intuition idtac.
      2: autounfold in *; simpl in *; intuition subst; eauto.

      destruct (a == r0).
      + step_prog; intros.
        exists tt; simpl; intuition idtac.
        2: autounfold in *; simpl in *; intuition subst; eauto.
        2: autounfold in *; simpl in *; intuition subst; eauto.

        step_prog; intros.
        eauto.

        simpl in *; intuition subst.
        2: autounfold in *; simpl in *; intuition subst; eauto.

        eauto.

      + step_prog; intros.
        exists tt; simpl; intuition idtac.
        2: autounfold in *; simpl in *; intuition subst; eauto.
        2: autounfold in *; simpl in *; intuition subst; eauto.

        step_prog; intros.
        eauto.

        simpl in *; intuition subst.
        2: autounfold in *; simpl in *; intuition subst; eauto.
        eauto.
  Qed.

  Theorem size_ok : prog_spec OneDiskAPI.size_spec size recover abstr.
  Proof.
    unfold diskSize.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.
    2: autounfold in *; simpl in *; intuition subst; eauto.

    step_prog; intros.
    eauto.

    simpl in *; intuition subst.
    2: autounfold in *; simpl in *; intuition subst; eauto.

    exists s. split. split. auto.
    2: auto.

    invert_abstraction.
    omega.
  Qed.

  Theorem recover_noop : rec_noop recover abstr no_wipe.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_prog; intros.
    eauto.

    destruct a; simpl in *.
    autounfold in *; intuition eauto.
    subst; eauto.
  Qed.

End RemappedDisk.


Require Import BadSectorImpl.
Module x := RemappedDisk BadSectorDisk.
Print Assumptions x.write_ok.
