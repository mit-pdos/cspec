Require Import POCS.
Require Import FSAPI.
Require Import MailServerAPI.
Import ListNotations.


Module MailServer (fs : FSAPI) <: MailServerAPI.


  Definition mail_abstraction (fs_state : FSAPI.State) (mail_state : MailServerAPI.State) : Prop :=
    True.

  Definition abstr : Abstraction MailServerAPI.State :=
    abstraction_compose
      fs.abstr
      {| abstraction := mail_abstraction |}.


  Definition deliver (user : nat) (m : message) : proc unit :=
    Ret tt.

  Definition read (user : nat) : proc mailbox :=
    Ret nil.

  Definition delete (user : nat) (idx : nat) : proc unit :=
    Ret tt.

  Definition newuser : proc nat :=
    Ret 0.


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
