Require Import POCS.
Require Import FSAPI.
Require Import MailServerAPI.
Require Import String.
Import ListNotations.


Module MailServer (fs : FSAPI) <: MailServerAPI.


  Definition mail_abstraction (fs_state : FSAPI.State) (mail_state : MailServerAPI.State) : Prop :=
    let fs := set_latest fs_state in
    set_older fs_state = nil /\
    forall uid mailbox, mail_state uid = Some mailbox ->
    exists dirnum,
    fs [uid] = Some (Dir dirnum) /\
    forall msg, In msg mailbox ->
    exists fn handle,
    fs [uid; fn] = Some (File handle (mk_file msg)).

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

    step_prog; intros.
    eauto.

    simpl in *; intuition.
  Qed.

  (** ** Exercise : complete the proof of [add] *)
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
