Require Import POCS.

Require Import String.
Require Import FS.SepLogic.Mem.
Require Import FS.SepLogic.Pred.

Require Import FSAPI.
Require Import MailServerAPI.


Module MailServer (fs : FSAPI) <: MailServerAPI.

  Import ListNotations.

  Fixpoint mailbox_pred (mbox : mailbox) (missing_pred : pred pathname tree_node) : pred pathname tree_node :=
    match mbox with
    | nil => missing_pred
    | m :: mbox' =>
      (exists pn handle,
       [pn] |-> File handle (mk_file m) *
       mailbox_pred mbox' (pred_except missing_pred [pn] Missing))%pred
    end.

  Definition user_pred (uid : string) (mbox : mailbox) : pred pathname tree_node :=
    (exists dirnum, [uid] |-> Dir dirnum *
     subtree_pred [uid] (mailbox_pred mbox empty_dir))%pred.

  Fixpoint user_mailbox_pred_m (users_and_mailboxes : list (user * mailbox)) : pred user mailbox :=
    match users_and_mailboxes with
    | nil => emp
    | (u, mbox) :: rest =>
      (u |-> mbox * user_mailbox_pred_m rest)%pred
    end.

  Fixpoint user_mailbox_pred_fs (users_and_mailboxes : list (user * mailbox)) (missing_users : pred pathname tree_node) : pred pathname tree_node :=
    match users_and_mailboxes with
    | nil => missing_users
    | (u, mbox) :: rest =>
      (user_pred u mbox * user_mailbox_pred_fs rest (pred_except missing_users [u] Missing))%pred
    end.


  Definition mail_abstraction (fs_state : FSAPI.State) (mail_state : MailServerAPI.State) : Prop :=
    let fs := set_latest fs_state in
    set_older fs_state = nil /\
    exists users_and_mailboxes maildirid tmpdirid Ftemp,
    mail_state |= user_mailbox_pred_m users_and_mailboxes /\
    fs |= subtree_pred maildir ([] |-> Dir maildirid * user_mailbox_pred_fs users_and_mailboxes empty_dir) *
          tmpdir |-> Dir tmpdirid * Ftemp.


  Definition abstr : Abstraction MailServerAPI.State :=
    abstraction_compose
      fs.abstr
      {| abstraction := mail_abstraction |}.


  Definition deliver (user : string) (m : message) : proc unit :=
    tmpname <- fs.find_available_name tmpdir;
    _ <- fs.create tmpdir tmpname;
    _ <- fs.write_logged (tmpdir ++ [tmpname]) m;
    fn <- fs.find_available_name (maildir ++ [user]);
    _ <- fs.rename_file (tmpdir ++ [tmpname]) (maildir ++ [user]) fn;
    Ret tt.

  Fixpoint read' (user : string) (files : list string) : proc mailbox :=
    match files with
    | nil => Ret nil
    | fn :: files' =>
      msg <- fs.read [user; fn];
      others <- read' user files';
      Ret (msg :: others)
    end.

  Definition read (user : string) : proc mailbox :=
    fns <- fs.readdir [user];
    mbox <- read' user fns;
    Ret mbox.

  Fixpoint delete' (user : string) (victim : string) (files : list string) : proc unit :=
    match files with
    | nil => Ret tt
    | fn :: files' =>
      _ <- delete' user victim files';
      msg <- fs.read [user; fn];
      if string_dec msg victim then
        fs.delete [user; fn]
      else
        Ret tt
    end.

  Definition delete (user : string) (m : string) : proc unit :=
    fns <- fs.readdir [user];
    _ <- delete' user m fns;
    Ret tt.

  Definition newuser : proc string :=
    fn <- fs.find_available_name maildir;
    _ <- fs.mkdir maildir fn;
    Ret fn.


  Definition init' : proc InitResult :=
    Ret Initialized.

  Definition init := then_init fs.init init'.

  Definition recover : proc unit :=
    fs.recover.


  Theorem init_ok : init_abstraction init recover abstr inited.
  Proof.
    eapply then_init_compose; eauto.
    unfold init'.

    step_proc; eauto; intros.
    simpl in *; intuition.

    exists (empty_mem).
    unfold inited; intuition.
    unfold FSAPI.inited in *.
    unfold mail_abstraction.
    intuition.

    exists nil; simpl.
    intuition.
  Admitted.


  Lemma extract_user : forall s F uid m users_and_mailboxes,
    s |= F * uid |-> m ->
    s |= user_mailbox_pred_m users_and_mailboxes ->
    exists um0 um1,
    users_and_mailboxes = um0 ++ (uid, m) :: um1.
  Admitted.

  Lemma extract_user_fs : forall um0 um1 uid m missingF,
    user_mailbox_pred_fs (um0 ++ (uid, m) :: um1) missingF ===>
    user_mailbox_pred_fs (um0 ++ um1) (pred_except missingF [uid] Missing) *
    user_pred uid m.
  Admitted.

  Lemma pred_eexcept_maildir_tmpdir : forall mp fn,
    pred_eexcept (subtree_pred maildir mp) (tmpdir ++ fn) ===>
    subtree_pred maildir mp.
  Admitted.


  Theorem deliver_ok :
    forall (uid : string) msg, proc_spec (deliver_spec uid msg) (deliver uid msg) recover abstr.
  Proof.
    unfold deliver.
    intros.

    apply spec_abstraction_compose; simpl.

    spec_intros.
    destruct a. destruct p. simpl in *.
    intuition.
    unfold mail_abstraction in *.
    intuition.
    repeat deex.

    eapply (extract_user _ H0) in H1.
    repeat deex.

    step_proc; intros; simpl in *; repeat deex.
    eexists (_, _); simpl; intuition idtac.

    eapply pimpl_apply; eauto.
    eapply pimpl_trans. apply star_comm.
    eapply pimpl_trans. apply star_assoc.
    reflexivity.

    step_proc; intros; simpl in *; repeat deex.
    eexists (_, _); simpl; intuition idtac.

    clear H2.
    eapply pimpl_apply; eauto.
    repeat rewrite subtree_pred_star.
    repeat rewrite pred_eexcept_star.
    repeat rewrite fs_concur_star.
    rewrite fs_concur_dir.
    replace (String "." suffix) with ("." ++ suffix)%string by reflexivity.
    rewrite fs_concur_tmp2.
    norm. cancel. denorm. reflexivity.

    step_proc; intros; simpl in *; repeat deex.
    eexists (_, _, _); simpl; intuition idtac.

    eapply pimpl_apply; eauto.
    repeat rewrite fs_concur_star.
    replace (String "." suffix) with ("." ++ suffix)%string by reflexivity.
    rewrite fs_concur_tmp1.
    norm. cancel. denorm. reflexivity.

    step_proc; intros; simpl in *; repeat deex.
    eapply pimpl_apply in H6.
    2: rewrite pred_eexcept_maildir_tmpdir.
    2: rewrite extract_user_fs.
    2: unfold user_pred.
    2: rewrite star_exists_r.
    2: rewrite star_exists_r.
    2: rewrite subtree_pred_exists.
    2: rewrite fs_concur_exists.
    2: rewrite fs_concur_exists.
    2: rewrite star_exists_r.
    2: rewrite star_exists_l.
    2: reflexivity.
    destruct H6.

    eexists (_, _); simpl; intuition idtac.

    eapply pimpl_apply; eauto.
    clear H2 H4 H3 H1 H5.
    repeat rewrite subtree_pred_star.
    rewrite subtree_pred_ptsto with (a := [uid]).
    repeat rewrite fs_concur_star.
    repeat rewrite fs_concur_dir.

    norm. cancel. denorm. reflexivity.

    step_proc; intros; simpl in *; repeat deex.
    eexists (_, _, _, _); simpl; intuition idtac.
    clear H2 H4 H3 H1 H5.
    eapply pimpl_apply; eauto.
    clear H8.

    repeat rewrite pred_eexcept_star.
    repeat rewrite fs_concur_star.
    rewrite pred_eexcept_ptsto_ne.
    repeat rewrite fs_concur_dir.
    replace (String "." suffix) with ("." ++ suffix)%string by reflexivity.
    rewrite fs_concur_tmp1.
    replace (String "." suffix0) with ("." ++ suffix0)%string by reflexivity.
    rewrite <- app_assoc.
    rewrite fs_concur_maildir.

    norm. cancel. denorm. reflexivity.
    admit.

    step_proc; intros; simpl in *; repeat deex.
    eexists; simpl; intuition idtac.

    

  Admitted.


  Theorem recover_noop : rec_noop recover abstr no_crash.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; intros.
    eauto.

    destruct a; simpl in *.
    intuition.
    eauto.
  Qed.

  Theorem read_ok : forall uid, proc_spec (read_spec uid) (read uid) recover abstr.
  Proof.
  Admitted.

  Theorem delete_ok : forall uid i, proc_spec (delete_spec uid i) (delete uid i) recover abstr.
  Proof.
  Admitted.

  Theorem newuser_ok : proc_spec newuser_spec newuser recover abstr.
  Proof.
  Admitted.

  (*
    TODO / future directions:

    - Finish a simple mail server.
      -- fix up separation logic (rewrite)
      -- extraction of real code
      -- crash safety: temp file rename, fsync, valuset model,
         recovery specs for FS and MailServer

    - Top-level security theorem.
    - Experiment with different security plans (Atalay's two plans).

    - Concurrency at the spec level using stable predicates.
      -- will require changing [find_available_name] to [create_available_name]
      -- test-and-set semantics; get logical ownership when create succeeds
    *)

End MailServer.

Require Import FSImpl.
Module MailServerImpl := MailServer FS.
