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

Axiom starts_with_tid_proper_name : forall tid name,
  starts_with_tid tid name ->
  proper_name name.

Hint Resolve starts_with_tid_proper_name.


(*
Module MailProtoExperiment <: LayerImpl MailLinkAPI MailServerLinkAPI.
*)

Definition deliver (user : string) (m : message) : proc _ _ :=
  cwd <- Op LinkGetRoot;
  tid <- Op GetTID;
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
  cwd <- Op LinkGetRoot;
  filenames <?- readdir cwd ([maildir; user]);
  read_files cwd ([maildir; user]) filenames.

Definition compile_op T (op : MailServerLinkAPI.opT T) : proc MailLinkAPI.opT T :=
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
  end.

Hint Extern 1 (MailLinkAPI.step _ _ _ _ _) => econstructor.
Hint Extern 1 (MailServerLinkAPI.step _ _ _ _ _) => econstructor.
Hint Extern 1 (LinkAPI.step _ _ _ _ _) => econstructor.
Hint Constructors mailfs_step_allowed.


(*
Definition proc_follows_protocol T (p : proc LinkAPI.opT T) (s : State) :=
  
*)

Inductive ts_follows_protocol (s : LinkAPI.State) (ts : @threads_state LinkAPI.opT) : Prop :=
| TSFP :
  (forall tid T (p : proc _ T) s' result evs,
    ts [[ tid ]] = Proc p ->
    exec_tid LinkAPI.step tid s p s' result evs ->
    exec_tid MailLinkAPI.step tid s p s' result evs /\
    ts_follows_protocol s' ts [[ tid :=
      match result with
      | inl v => NoProc
      | inr p' => Proc p'
      end ]]) ->
  ts_follows_protocol s ts.

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
