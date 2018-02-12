Require Import POCS.
Require Import FSModel.
Require Import LinkAPI.
Require Import FSAPI.
Require Import MailServerAPI.

Import ListNotations.
Require Import String.
Open Scope string.
Open Scope list.

(* End-to-end layering plan:

  MailServerAPI
    |
    | prove that our file system state matches the rep invariant
    |
  MailServerLinkAPI
    |
    | prove atomicity of our code implementing mail server opcodes;
    | no state abstraction yet
    |
  MailLinkAPI
    |
    | prove that our code follows the [mailfs_step_allowed]
    | protocol and maintains the invariant
    |
  LinkAPI
    |
    | adds LinkFindUnusedName, need to prove
    |
  BaseLinkAPI (not defined yet)

*)


Definition maildir := "mail".
Definition tmpdir := "tmp".

Global Opaque maildir.
Global Opaque tmpdir.

Parameter tid_to_string : nat -> string.

Definition starts_with_tid tid (name : string) : Prop :=
  exists namesuffix,
    name = (tid_to_string tid ++ "." ++ namesuffix)%string.


Inductive mailfs_step_allowed : forall T, linkOpT T -> nat -> LinkAPI.State -> Prop :=
| MailAllowLinkAllocFile : forall dirnum name tid fs_state,
  starts_with_tid tid name ->
  path_eval_root fs_state [tmpdir] (DirNode dirnum) ->
  mailfs_step_allowed (LinkAllocFile dirnum name) tid fs_state

| MailAllowLinkLookupRoot : forall dirnum name tid fs_state,
  dirnum = FSRoot fs_state ->
  proper_name name ->
  mailfs_step_allowed (LinkLookup dirnum name) tid fs_state

| MailAllowLinkLookupTmp : forall dirnum name tid fs_state,
  starts_with_tid tid name ->
  path_eval_root fs_state [tmpdir] (DirNode dirnum) ->
  proper_name name ->
  mailfs_step_allowed (LinkLookup dirnum name) tid fs_state

| MailAllowLinkLookupMail : forall dirnum name tid fs_state,
  path_eval_root fs_state [maildir] (DirNode dirnum) ->
  proper_name name ->
  mailfs_step_allowed (LinkLookup dirnum name) tid fs_state

| MailAllowLinkLookupUser : forall dirnum name tid fs_state user f,
  path_eval_root fs_state [maildir; user] (DirNode dirnum) ->
  proper_name name ->
  valid_link fs_state dirnum name (FileNode f) ->
  mailfs_step_allowed (LinkLookup dirnum name) tid fs_state

| MailAllowFileWrite : forall name tid fs_state f data,
  starts_with_tid tid name ->
  path_eval_root fs_state [tmpdir; name] (FileNode f) ->
  mailfs_step_allowed (FileWrite f data) tid fs_state

| MailAllowFileRead : forall user name tid fs_state f,
  path_eval_root fs_state [maildir; user; name] (FileNode f) ->
  mailfs_step_allowed (FileRead f) tid fs_state

| MailAllowRenameAdd : forall dirnum name f tid fs_state user,
  starts_with_tid tid name ->
  path_eval_root fs_state [maildir; user] (DirNode dirnum) ->
  (~ exists target, valid_link fs_state dirnum name target) ->
  mailfs_step_allowed (LinkAdd dirnum name (FileNode f)) tid fs_state

| MailAllowRenameDel : forall dirnum name f tid fs_state,
  starts_with_tid tid name ->
  path_eval_root fs_state [tmpdir] (DirNode dirnum) ->
  valid_link fs_state dirnum name (FileNode f) ->
  mailfs_step_allowed (LinkDel dirnum name (FileNode f)) tid fs_state

| MailAllowReaddir : forall dirnum tid fs_state user,
  path_eval_root fs_state [maildir; user] (DirNode dirnum) ->
  mailfs_step_allowed (LinkList dirnum) tid fs_state

| MailAllowFindUser : forall dirnum tid fs_state user pfx,
  starts_with_tid tid pfx ->
  path_eval_root fs_state [maildir; user] (DirNode dirnum) ->
  mailfs_step_allowed (LinkFindUnusedName dirnum pfx) tid fs_state

| MailAllowFindTmp : forall dirnum tid fs_state pfx,
  starts_with_tid tid pfx ->
  path_eval_root fs_state [tmpdir] (DirNode dirnum) ->
  mailfs_step_allowed (LinkFindUnusedName dirnum pfx) tid fs_state

| MailAllowGetTID : forall state tid,
  mailfs_step_allowed GetTID tid state

| MailAllowLinkGetRoot : forall state tid,
  mailfs_step_allowed LinkGetRoot tid state.


Definition unique_dir_pn (fs : FS) :=
  forall pn0 pn1 d,
    path_eval_root fs pn0 (DirNode d) ->
    path_eval_root fs pn1 (DirNode d) ->
    pn0 = pn1.

Definition unique_pn_dir (fs : FS) :=
  forall pn d1 d2,
    path_eval_root fs pn (DirNode d1) ->
    path_eval_root fs pn (DirNode d2) ->
    d1 = d2.

Definition invariant (fs : FS) :=
  unique_dir_pn fs /\
  unique_pn_dir fs /\
  unique_pathname_root fs [tmpdir] /\
  proper_pathname_root fs [tmpdir] /\
  unique_pathname_root fs [maildir] /\
  proper_pathname_root fs [maildir] /\
  forall user,
    maybe_unique_pathname_root fs [maildir; user] /\
    proper_pathname_root fs [maildir; user].


Module MailLinkAPI <: Layer.

  Definition opT := linkOpT.
  Definition State := FS.

  Definition step T (op : linkOpT T) tid s r s' :=
    LinkAPI.step op tid s r s' /\
    mailfs_step_allowed op tid s /\
    invariant s /\
    invariant s'.

  Definition initP (fs : State) := invariant fs.

End MailLinkAPI.


Module MailServerLinkAPI <: Layer.

  Definition opT := mailOpT.
  Definition State := FS.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> Prop :=
  | StepDeliver : forall user msg state tid userdirnum msgf name state',
    path_eval_root state [maildir; user] (DirNode userdirnum) ->
    starts_with_tid tid name ->
    (~ exists target, path_eval_root state [maildir; user; name] target) ->
    file_handle_valid state msgf ->
    file_handle_unused state msgf ->
    state' = create_file_write userdirnum msgf name msg state ->
    xstep (Deliver user msg) tid
      state
      (Some tt)
      state'
  | StepRead : forall user msgs state tid,
    (forall msg,
      In msg msgs <->
      exists name f,
        path_eval_root state [maildir; user; name] (FileNode f) /\
        nth_error (FSFiles state) f = Some msg) ->
    xstep (Read user) tid
      state
      (Some msgs)
      state
  | StepFail : forall T (op : opT (option T)) state tid,
    xstep op tid
      state
      None
      state.

  Definition step := xstep.

  Definition initP (fs : State) := invariant fs.

End MailServerLinkAPI.
