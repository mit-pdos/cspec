Require Import POCS.
Require Import FSModel.
Require Import LinkAPI.
Require Import FSAPI.
Require Import MailServerAPI.
Require Import MailServerLayers.

Import ListNotations.
Require Import String.
Open Scope string.
Open Scope list.


(*
Module MailProtoExperiment <: LayerImpl MailLinkAPI MailServerLinkAPI.
*)

Definition deliver (user : string) (m : message) : proc _ _ :=
  cwd <- Prim LinkGetRoot;
  tid <- Prim GetTID;
  tmpname <?- find_available_name cwd [tmpdir] (tid_to_string tid);
  f <?- create cwd [tmpdir] tmpname;
  _ <?- write cwd ([tmpdir; tmpname]) m;
  msgname <?- find_available_name cwd ([maildir; user]) (tid_to_string tid);
  _ <?- rename cwd [tmpdir] tmpname ([maildir; user]) msgname;
  Ret (Some tt).

Fixpoint read_files (cwd : nat) (dir : Pathname) (files : list string) : proc _ (option (list message)) :=
  match files with
  | nil => Ret (Some nil)
  | fn :: files' =>
    msg <?- read cwd (dir ++ [fn]);
    others <?- read_files cwd dir files';
    Ret (Some (msg :: others))
  end.

Definition read (user : string) : proc _ _ :=
  cwd <- Prim LinkGetRoot;
  filenames <?- readdir cwd ([maildir; user]);
  read_files cwd ([maildir; user]) filenames.

Definition compile_op T (op : MailServerLinkAPI.Op T) : proc MailLinkAPI.Op T :=
  match op with
  | Deliver user msg => deliver user msg
  | Read user => read user
  end.

Ltac step_inv :=
  match goal with
  | H : MailLinkAPI.step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : MailServerLinkAPI.step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : mailfs_step_allowed _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : LinkAPI.step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : restricted_step _ _ _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.

Hint Extern 1 (MailLinkAPI.step _ _ _ _ _) => econstructor.
Hint Extern 1 (MailServerLinkAPI.step _ _ _ _ _) => econstructor.
Hint Extern 1 (LinkAPI.step _ _ _ _ _) => econstructor.
Hint Constructors mailfs_step_allowed.


Hint Constructors follows_protocol_proc.

Theorem restricted_step_preserves_invariant :
  forall tid `(op : LinkAPI.Op T) s r s',
    restricted_step LinkAPI.step mailfs_step_allowed op tid s r s' ->
    invariant s ->
    invariant s'.
Proof.
  intros.
  destruct H; intuition idtac; subst; eauto.
  repeat step_inv; eauto.
  - split.
    unfold unique_dir_pn. admit.
    unfold unique_pn_node. admit.
  - admit.
  - admit.
  - split.
    unfold unique_dir_pn. admit.
    unfold unique_pn_node. admit.
Admitted.

Theorem restricted_step_preserves_root :
  forall tid `(op : LinkAPI.Op T) s r s',
    restricted_step LinkAPI.step mailfs_step_allowed op tid s r s' ->
    FSRoot s = FSRoot s'.
Proof.
  intros.
  destruct H; intuition idtac; subst; eauto.
  repeat step_inv; eauto.
Qed.

Theorem exec_others_preserves_invariant :
  forall tid s s',
    exec_others LinkAPI.step mailfs_step_allowed tid s s' ->
    invariant s ->
    invariant s'.
Proof.
  induction 1; intros; eauto.
  repeat deex.
  clear H0.
  eapply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
  clear H.
  eapply restricted_step_preserves_invariant; eauto.
Qed.

Theorem exec_others_preserves_root :
  forall tid s s',
    exec_others LinkAPI.step mailfs_step_allowed tid s s' ->
    FSRoot s = FSRoot s'.
Proof.
  induction 1; intros; eauto.
  repeat deex.
  clear H0.
  rewrite <- IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
  clear H.
  eapply restricted_step_preserves_root; eauto.
Qed.


Ltac exec_propagate :=
  match goal with
(*
  | s : RawLockAPI.State |- _ =>
    destruct s
*)
  | H : exec_any _ _ _ _ (Prim _) _ _ |- _ =>
    eapply exec_any_op in H; repeat deex
  | H : exec_others _ _ _ ?s _,
    Hi : invariant ?s |- _ =>
    eapply exec_others_preserves_invariant in Hi; [ | exact H ]
  | H : exec_others _ _ _ ?s _,
    Hi : context[FSRoot ?s] |- _ =>
    rewrite (exec_others_preserves_root H) in Hi
  | H : restricted_step _ _ _ _ ?s _ _,
    Hi : invariant ?s |- _ =>
    eapply restricted_step_preserves_invariant in Hi; [ | exact H ]
  end.

Ltac clear_allowed :=
  match goal with
  | H: mailfs_step_allowed _ _ _ |- _ =>
    clear H
  end.

Definition loopInv (s : FS) (tid : nat) := True.

Lemma namei_maildir_user :
  forall s r user tid,
    r = FSRoot s ->
    follows_protocol_proc LinkAPI.step mailfs_step_allowed loopInv
      tid s (namei_spec (DirNode r) [maildir; user]).
Proof.
  intros.
  constructor; intros.

  constructor. constructor; eauto.

  repeat exec_propagate.
  step_inv. clear_allowed. repeat step_inv.

  constructor.

  destruct target; try constructor; intros.
  constructor. eapply MailAllowLinkLookupMail.
    econstructor; eauto. constructor.

  repeat exec_propagate.
  step_inv. clear_allowed. repeat step_inv.

  constructor.
  constructor.
Qed.

Lemma read_follows_protocol : forall tid s user,
  follows_protocol_proc LinkAPI.step mailfs_step_allowed loopInv tid s (read user).
Proof.
  intros.
  constructor; intros.
    constructor; intros. eauto.

  repeat exec_propagate.
  repeat step_inv.

  constructor; intros.
  constructor; intros.
  constructor; intros.
  eapply namei_maildir_user; eauto.

  destruct r; try constructor.
  destruct n; constructor.
  destruct r; try constructor.

  repeat exec_propagate.
  econstructor.

  constructor; intros.
    constructor; intros.
  
    constructor; intros. eauto.

  repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
  constructor; intros.
    constructor; intros. eauto.

  repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
  constructor; intros.
    constructor; intros. eauto.

  repeat exec_propagate.
    unfold restricted_step in *; intuition idtac; repeat step_inv.
  constructor; intros.
Qed.


Theorem compile_follows_protocol : forall s ts,
  ts_follows_protocol s (compile_ts compile_op ts).
Admitted.

Definition absR (s1 : LinkAPI.State) (s2 : MailLinkAPI.State) :=
  s1 = s2.

Theorem top_level :
  forall ts,
    traces_match_abs absR LinkAPI.initP LinkAPI.step MailLinkAPI.step
      (compile_ts compile_op ts)
      (compile_ts compile_op ts).
Proof.
  unfold absR.
  unfold traces_match_abs; intros.
  subst.
  clear H.
  assert (ts_follows_protocol sm (compile_ts compile_op ts)).
    apply compile_follows_protocol.
  generalize dependent (compile_ts compile_op ts); intros.
  destruct H0.
  induction H0; intros; subst.
  - inversion H; clear H.
    edestruct H3; eauto.
    edestruct IHexec.
      eauto.
    intuition idtac.
    eexists; split.
    + eapply ExecPrefixOne with (tid := tid).
        eauto.
        eauto.
      eassumption.
    + eauto.
  - eauto.
Qed.
