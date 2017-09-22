Require Import POCS.

Import ListNotations.
Require Import String.
Require Import FS.SepLogic.Mem.
Require Import FS.SepLogic.Pred.

Require Import FSAPI.
Require Import MailServerAPI.


Module MailServer (fs : FSAPI) <: MailServerAPI.


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
    exists users_and_mailboxes,
    mail_state |= user_mailbox_pred_m users_and_mailboxes /\
    fs |= [] |-> Dir 0 * user_mailbox_pred_fs users_and_mailboxes empty_dir.


  Definition abstr : Abstraction MailServerAPI.State :=
    abstraction_compose
      fs.abstr
      {| abstraction := mail_abstraction |}.


  Axiom find_available_name : pathname -> proc string.

  Definition deliver (user : string) (m : message) : proc unit :=
    fn <- find_available_name [user];
    _ <- fs.create [user] fn;
    _ <- fs.write_logged [user; fn] m;
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
    fn <- find_available_name [];
    _ <- fs.mkdir [] fn;
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

    step_prog; eauto; intros.
    simpl in *; intuition.

    exists (empty_mem).
    unfold inited; intuition.
    unfold FSAPI.inited in *.
    unfold mail_abstraction.
    intuition.

    exists nil; simpl.
    intuition.
    firstorder.
  Qed.

  Theorem add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
  Proof.
    unfold add.
    intros.

    apply spec_abstraction_compose; simpl.
  (* SOL *)
    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    eexists (_, _); simpl; intuition idtac.

    step_prog; intros.
    eexists (_, _); simpl; intuition idtac.

    step_prog; intros.
    eexists (_, _); simpl; intuition idtac.

    step_prog; intros.
    eexists (_, _); simpl; intuition idtac.

    step_prog; intros.
    eauto.

    simpl in *; intuition subst.

    eexists; intuition auto.
    unfold statdb_abstraction in *; simpl in *.
    intuition omega.

    autounfold in *; intuition.
  Qed.
  (* END *)
  (* STUB: Admitted. *)    

  (** ** Exercise : complete the proof of [mean] *)
  Theorem mean_ok : proc_spec mean_spec mean recover abstr.
  Proof.
    unfold mean.
    intros.

    apply spec_abstraction_compose; simpl.

  (* SOL *)
    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    eexists (_, _); simpl; intuition idtac.

    destruct (r == 0).

    - step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: autounfold in *; intuition.

      unfold statdb_abstraction in *.
      destruct s; intuition; simpl in *; try congruence.
      exists nil; intuition auto.

    - step_prog; intros.
      eexists (_, _); simpl; intuition idtac.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: autounfold in *; intuition.

      unfold statdb_abstraction in *.
      destruct s; intuition.

      eexists; intuition auto.
      right.
      intuition ( try congruence ).
  Qed.
  (* END *)
  (* STUB: Admitted. *)    


  Theorem recover_noop : rec_noop recover abstr no_crash.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_prog; intros.
    eauto.

    destruct a; simpl in *.
    intuition.
    eauto.
  Qed.

End MailServer.
