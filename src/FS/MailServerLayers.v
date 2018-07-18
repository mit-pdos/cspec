Require Import CSPEC.
Require Import FSModel.
Require Import LinkAPI.
Require Import FSAPI.
Require Import MailServerAPI.
Require Import FMapInterface.
Require Import FMapAVL.
Require Import OrderedTypeEx.

Import ListNotations.
Require Import String.
Open Scope string.
Open Scope list.


(* Abstraction: directories are limited to [tmp] or [mail; user] *)

Module LinkDirAPI <: Layer.

  Inductive user :=
  | User0
  | User1.

  Inductive mfs_dir :=
  | MFStmp : mfs_dir
  | MFSuser : forall (u : user), mfs_dir.


  Instance mfs_dir_equal : EqualDec mfs_dir.
  Admitted.

(*
  Module mfs_dir_as_OT <: UsualOrderedType.
    Definition t := mfs_dir.

    Definition eq := @eq t.
    Definition eq_refl := @eq_refl t.
    Definition eq_sym := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    Definition lt (x y : t) : Prop.
    Admitted.

    Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Admitted.

    Theorem lt_not_eq : forall x y, lt x y -> ~ eq x y.
    Admitted.

    Definition compare x y : OrderedType.Compare lt eq x y.
    Proof.
    Admitted.

    Definition eq_dec : forall (x y : t), {x=y}+{x<>y}.
    Admitted.

  End mfs_dir_as_OT.

  Module Dirs := FMapAVL.Make(mfs_dir_as_OT).
*)

  Module DirContents := FMapAVL.Make(String_as_OT).

  Definition mfs_dir_contents := DirContents.t nat.

  Record mfs_state := mkMFS {
    MFSLinks : mfs_dir -> mfs_dir_contents;
    MFSFiles : Files;
  }.

  Definition State := mfs_state.

  Inductive mfs_opT : Type -> Type :=
  | FindAvailable (pfx : string) (d : mfs_dir) : mfs_opT (option string)
  | CreateFile (d : mfs_dir) (fn : string) : mfs_opT (option nat)
  | FileRead (f : nat) : mfs_opT (option string)
  | FileWrite (f : nat) (data : string) : mfs_opT (option unit)
  | LinkToUser (srcfn : string) (dstfn : string) (user : string) : mfs_opT (option unit)
  | UnlinkTmp (fn : string) : mfs_opT (option unit)
  | ListUser (user : string) : mfs_opT (option (list string))
  | LookupUser (user : string) (fn : string) : mfs_opT (option nat).

  Definition Op := mfs_opT.

  Definition initP (s : State) := True.

  Definition file_handle_unused (fs : State) h :=
    ~ exists d name, DirContents.find name ((MFSLinks fs) d) = Some h.

  Definition file_handle_valid (fs : State) h :=
    h < Datatypes.length (MFSFiles fs).

  Definition add_link dir fid name (fs : State) :=
    mkMFS
      (fun d' =>
        if d' == dir then
          DirContents.add name fid (MFSLinks fs dir)
        else
          MFSLinks fs d')
      (MFSFiles fs).

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> Prop :=
(*
  | StepFindAvailable : forall pfx d state res tid,
    DirContents.find res ((MFSLinks state) d) = None ->
    xstep (FindAvailable pfx d) tid
      state
      (Some res)
      state
*)
  | StepCreateFile : forall d fn state fid tid,
    DirContents.find fn ((MFSLinks state) d) = None ->
    file_handle_valid state fid ->
    file_handle_unused state fid ->
    xstep (CreateFile d fn) tid
      state
      (Some fid)
      (add_link d fid fn state)
  .

  Definition step := xstep.

End LinkDirAPI.


Module LinkDirStableAPI <: Layer.

  Definition Op := LinkAPI.Op.
  Definition State := LinkAPI.State.
  Definition initP := LinkAPI.initP.

  Inductive op_allow : forall T, linkOpT T -> nat -> LinkAPI.State -> Prop :=
  | OpAllowLinkAllocFile : forall dirnum name tid fs_state,
    op_allow (LinkAllocFile dirnum name) tid fs_state

  | OpAllowLinkLookup : forall dirnum name tid fs_state,
    op_allow (LinkLookup dirnum name) tid fs_state

  | OpAllowFileWrite : forall tid fs_state f data,
    op_allow (FileWrite f data) tid fs_state

  | OpAllowFileRead : forall tid fs_state f,
    op_allow (FileRead f) tid fs_state

  | OpAllowLinkTmp : forall dirnum dirname name f tid fs_state,
    path_eval_root fs_state [dirname] (DirNode dirnum) ->
    op_allow (LinkAdd dirnum name (FileNode f)) tid fs_state

  | OpAllowUnlink : forall dirnum dirname name f tid fs_state,
    path_eval_root fs_state [dirname] (DirNode dirnum) ->
    valid_link fs_state dirnum name (FileNode f) ->
    op_allow (LinkDel dirnum name (FileNode f)) tid fs_state

  | OpAllowReaddir : forall dirnum tid fs_state,
    op_allow (LinkList dirnum) tid fs_state

(*
  | MailAllowFindUser : forall dirnum tid fs_state user pfx,
    starts_with_tid tid pfx ->
    path_eval_root fs_state [maildir; user] (DirNode dirnum) ->
    mailfs_step_allowed (LinkFindUnusedName dirnum pfx) tid fs_state

  | MailAllowFindTmp : forall dirnum tid fs_state pfx,
    starts_with_tid tid pfx ->
    path_eval_root fs_state [tmpdir] (DirNode dirnum) ->
    mailfs_step_allowed (LinkFindUnusedName dirnum pfx) tid fs_state
*)

  | OpAllowGetTID : forall state tid,
    op_allow GetTID tid state

  | OpAllowLinkGetRoot : forall state tid,
    op_allow LinkGetRoot tid state
  .

  Definition step := nilpotent_step LinkAPI.step op_allow.

  Definition loopInv (s : State) (tid : nat) := True.

End LinkDirStableAPI.


Module Dirs <: LayerImpl LinkDirAPI LinkAPI.

  Import LinkDirAPI.

  Definition user_to_dirname (u : user) :=
    match u with
    | User1 => "user1"
    | User2 => "user2"
    end.

  Definition dir_to_pn (d : mfs_dir) :=
    [ match d with
      | MFStmp => "tmp"
      | MFSuser u => user_to_dirname u
      end ].

  Definition create_file_core (d : mfs_dir) (fn : string) :=
    cwd <- Call LinkGetRoot;
    f <?- create cwd (dir_to_pn d) fn;
    Ret (Some f).


  Ltac step_inv :=
    match goal with
    | H : LinkDirStableAPI.op_allow _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : LinkAPI.step _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : restricted_step _ _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end.

  Hint Extern 1 (LinkAPI.step _ _ _ _ _) => econstructor.
  Hint Constructors LinkDirStableAPI.op_allow.


  Theorem restricted_step_preserves_root :
    forall tid `(op : LinkAPI.Op T) s r s',
      restricted_step LinkAPI.step LinkDirStableAPI.op_allow op tid s r s' ->
      FSRoot s = FSRoot s'.
  Proof.
    intros.
    destruct H; intuition idtac; subst; eauto.
    repeat step_inv; eauto.
  Qed.

  Theorem exec_others_preserves_root :
    forall tid s s',
      exec_others LinkAPI.step LinkDirStableAPI.op_allow tid s s' ->
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
    | H : exec_any _ _ _ _ (Call _) _ _ |- _ =>
      eapply exec_any_op in H; repeat deex
    | H : exec_others _ _ _ ?s _,
      Hi : context[FSRoot ?s] |- _ =>
      rewrite (exec_others_preserves_root H) in Hi
    end.

  Ltac clear_allowed :=
    match goal with
    | H: LinkDirStableAPI.op_allow _ _ _ |- _ =>
      clear H
    end.


  Theorem create_file_follows_protocol : forall tid s d fn,
    follows_protocol_proc LinkAPI.step LinkDirStableAPI.op_allow LinkDirStableAPI.loopInv
      tid s (create_file_core d fn).
  Proof.
    intros.
    constructor; intros.
      constructor. constructor.

    repeat exec_propagate.
    step_inv. clear_allowed. step_inv.

    constructor; intros.
    constructor; intros.
    constructor; intros.
    constructor; intros.
    constructor. constructor.
    destruct r; constructor.
    destruct r; try constructor.
    destruct n; try constructor.
    destruct r; try constructor.
    constructor.
    destruct r; try constructor.
  Qed.

End Dirs.


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


Parameter tid_to_string : nat -> string.

Definition starts_with_tid tid (name : string) : Prop :=
  exists namesuffix,
    name = (tid_to_string tid ++ "." ++ namesuffix)%string.


Inductive mailfs_step_allowed : forall T, linkOpT T -> nat -> LinkAPI.State -> Prop :=
| MailAllowLinkAllocFile : forall dirnum name tid fs_state,
  starts_with_tid tid name ->
  path_eval_root fs_state [tmpdir] (DirNode dirnum) ->
  (~ exists target, valid_link fs_state dirnum name target) ->
  mailfs_step_allowed (LinkAllocFile dirnum name) tid fs_state

| MailAllowLinkLookupRoot : forall dirnum name tid fs_state,
  dirnum = FSRoot fs_state ->
  mailfs_step_allowed (LinkLookup dirnum name) tid fs_state

| MailAllowLinkLookupTmp : forall dirnum name tid fs_state,
  starts_with_tid tid name ->
  path_eval_root fs_state [tmpdir] (DirNode dirnum) ->
  mailfs_step_allowed (LinkLookup dirnum name) tid fs_state

| MailAllowLinkLookupMail : forall dirnum name tid fs_state,
  path_eval_root fs_state [maildir] (DirNode dirnum) ->
  mailfs_step_allowed (LinkLookup dirnum name) tid fs_state

| MailAllowLinkLookupUser : forall dirnum name tid fs_state user f,
  path_eval_root fs_state [maildir; user] (DirNode dirnum) ->
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

Definition unique_pn_node (fs : FS) :=
  forall pn n1 n2,
    path_eval_root fs pn n1 ->
    path_eval_root fs pn n2 ->
    n1 = n2.

Definition exists_dir (fs : FS) (pn : Pathname) :=
  exists dirnum,
    path_eval_root fs pn (DirNode dirnum).

Definition invariant (fs : FS) :=
  unique_dir_pn fs /\
  unique_pn_node fs.


Module MailLinkAPI <: Layer.

  Definition Op := linkOpT.
  Definition State := FS.

  Definition step T (op : linkOpT T) tid s r s' :=
    LinkAPI.step op tid s r s' /\
    mailfs_step_allowed op tid s /\
    invariant s /\
    invariant s'.

  Definition initP (fs : State) := invariant fs.

End MailLinkAPI.


Module MailServerLinkAPI <: Layer.

  Definition Op := mailOpT.
  Definition State := FS.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> Prop :=
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
  | StepFail : forall T (op : Op (option T)) state tid,
    xstep op tid
      state
      None
      state.

  Definition step := xstep.

  Definition initP (fs : State) := invariant fs.

End MailServerLinkAPI.
