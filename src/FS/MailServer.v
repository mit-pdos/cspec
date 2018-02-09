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


Axiom starts_with_tid_proper_name : forall tid name,
  starts_with_tid tid name ->
  proper_name name.

Hint Resolve starts_with_tid_proper_name.


Module MailAtomic <: LayerImpl MailLinkAPI MailServerLinkAPI.

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


  Lemma link_get_root_right_mover :
    right_mover MailLinkAPI.step LinkGetRoot.
  Proof.
    unfold right_mover; intros.
    inversion H0; clear H0.
    inversion H2; clear H2; repeat sigT_eq.
    eexists; split; eauto.
    repeat ( step_inv; intuition idtac ).
    all: eauto.
  Qed.

  Lemma get_tid_right_mover :
    right_mover MailLinkAPI.step GetTID.
  Proof.
    unfold right_mover; intros.
    inversion H0; clear H0.
    inversion H2; clear H2; repeat sigT_eq.
    eexists; split; eauto.
    repeat ( step_inv; intuition idtac ).
    all: eauto.
  Qed.

  Lemma valid_link_add_link : forall fs dirnum name target dirnum0 name0 target0,
    valid_link (add_link dirnum0 target0 name0 fs) dirnum name target ->
    dirnum <> dirnum0 ->
    proper_name name ->
    proper_name name0 ->
    valid_link fs dirnum name target.
  Proof.
  Admitted.

  Lemma valid_link_add_link' : forall fs dirnum name target dirnum0 name0 target0,
    valid_link fs dirnum name target ->
    dirnum <> dirnum0 ->
    proper_name name ->
    proper_name name0 ->
    valid_link (add_link dirnum0 target0 name0 fs) dirnum name target.
  Proof.
  Admitted.

  Lemma valid_link_del_link : forall fs dirnum name target dirnum0 name0 target0,
    valid_link (del_link dirnum0 target0 name0 fs) dirnum name target ->
    dirnum <> dirnum0 ->
    proper_name name ->
    proper_name name0 ->
    valid_link fs dirnum name target.
  Proof.
  Admitted.

  Lemma valid_link_del_link' : forall fs dirnum name target dirnum0 name0 target0,
    valid_link fs dirnum name target ->
    dirnum <> dirnum0 ->
    proper_name name ->
    proper_name name0 ->
    valid_link (del_link dirnum0 target0 name0 fs) dirnum name target.
  Proof.
  Admitted.

  Lemma valid_link_upd_file : forall fs dirnum name target f data,
    valid_link (upd_file f data fs) dirnum name target ->
    proper_name name ->
    valid_link fs dirnum name target.
  Proof.
  Admitted.

  Lemma valid_link_upd_file' : forall fs dirnum name target f data,
    valid_link fs dirnum name target ->
    proper_name name ->
    valid_link (upd_file f data fs) dirnum name target.
  Proof.
  Admitted.

  Hint Extern 1 (valid_link ?fs ?dir ?name ?target) =>
    match goal with
    | H : valid_link (upd_file _ _ fs) dir name _ |- _ =>
      eapply valid_link_upd_file
    end.

  Hint Extern 1 (valid_link ?fs ?dir ?name ?target) =>
    match goal with
    | H : valid_link (del_link _ _ _ fs) dir name _ |- _ =>
      eapply valid_link_del_link
    end.

  Hint Extern 1 (valid_link ?fs ?dir ?name ?target) =>
    match goal with
    | H : valid_link (add_link _ _ _ fs) dir name _ |- _ =>
      eapply valid_link_add_link
    end.

  Hint Resolve valid_link_add_link'.
  Hint Resolve valid_link_del_link'.
  Hint Resolve valid_link_upd_file'.

  Lemma valid_link_add_link_ne_name : forall fs dirnum name target dirnum0 name0 target0,
    valid_link (add_link dirnum0 target0 name0 fs) dirnum name target ->
    name <> name0 ->
    proper_name name ->
    proper_name name0 ->
    valid_link fs dirnum name target.
  Proof.
  Admitted.

  Lemma valid_link_del_link_ne_name : forall fs dirnum name target dirnum0 name0 target0,
    valid_link (del_link dirnum0 target0 name0 fs) dirnum name target ->
    name <> name0 ->
    proper_name name ->
    proper_name name0 ->
    valid_link fs dirnum name target.
  Proof.
  Admitted.

  Lemma valid_link_add_link_ne_name' : forall fs dirnum name target dirnum0 name0 target0,
    valid_link fs dirnum name target ->
    name <> name0 ->
    proper_name name ->
    proper_name name0 ->
    valid_link (add_link dirnum0 target0 name0 fs) dirnum name target.
  Proof.
  Admitted.

  Lemma valid_link_del_link_ne_name' : forall fs dirnum name target dirnum0 name0 target0,
    valid_link fs dirnum name target ->
    name <> name0 ->
    proper_name name ->
    proper_name name0 ->
    valid_link (del_link dirnum0 target0 name0 fs) dirnum name target.
  Proof.
  Admitted.

  Hint Extern 1 (valid_link ?fs ?dir ?name ?target) =>
    match goal with
    | H : valid_link (add_link _ _ _ fs) dir name _ |- _ =>
      eapply valid_link_add_link_ne_name
    end.

  Hint Extern 1 (valid_link ?fs ?dir ?name ?target) =>
    match goal with
    | H : valid_link (del_link _ _ _ fs) dir name _ |- _ =>
      eapply valid_link_del_link_ne_name
    end.

  Hint Resolve valid_link_add_link_ne_name'.
  Hint Resolve valid_link_del_link_ne_name'.

  Axiom starts_with_tid_ne : forall tid0 tid1 name0 name1,
    starts_with_tid tid0 name0 ->
    starts_with_tid tid1 name1 ->
    tid0 <> tid1 ->
    name0 <> name1.

  Hint Resolve starts_with_tid_ne.


  Lemma path_eval_root_add_link_file : forall fs pn dirnum dirnum0 f name0,
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root (add_link dirnum0 (FileNode f) name0 fs) pn (DirNode dirnum).
  Admitted.

  Lemma path_eval_root_del_link_file : forall fs pn dirnum dirnum0 f name0,
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root (del_link dirnum0 (FileNode f) name0 fs) pn (DirNode dirnum).
  Admitted.

  Lemma path_eval_root_upd_file : forall fs pn dirnum f data,
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root (upd_file f data fs) pn (DirNode dirnum).
  Admitted.

  Hint Resolve path_eval_root_add_link_file.
  Hint Resolve path_eval_root_del_link_file.
  Hint Resolve path_eval_root_upd_file.


  Lemma proper_pathname_distinct : forall s pn d0 d1,
    path_evaluates s (DirNode d0) pn (DirNode d1) ->
    proper_pathname s d0 pn ->
    pn <> nil ->
    d0 <> d1.
  Admitted.

  Lemma proper_pathname_distinct_root : forall s pn d1,
    path_eval_root s pn (DirNode d1) ->
    proper_pathname_root s pn ->
    pn <> nil ->
    FSRoot s <> d1.
  Proof.
    unfold path_eval_root; intros.
    eapply proper_pathname_distinct; eauto.
  Qed.

  Lemma proper_pathname_distinct_tmpdir : forall s d1,
    path_eval_root s [tmpdir] (DirNode d1) ->
    invariant s ->
    FSRoot s <> d1.
  Proof.
    unfold invariant; intuition idtac.
    eapply proper_pathname_distinct_root; eauto.
    congruence.
  Qed.

  Lemma proper_pathname_distinct_maildir : forall s d1,
    path_eval_root s [maildir] (DirNode d1) ->
    invariant s ->
    FSRoot s <> d1.
  Proof.
    unfold invariant; intuition idtac.
    eapply proper_pathname_distinct_root; eauto.
    congruence.
  Qed.

  Lemma proper_pathname_distinct_userdir : forall s user d1,
    path_eval_root s [maildir; user] (DirNode d1) ->
    invariant s ->
    FSRoot s <> d1.
  Proof.
    unfold invariant; intuition idtac.
    eapply proper_pathname_distinct_root; eauto.
    edestruct H8; eauto.
    congruence.
  Qed.

  Hint Resolve proper_pathname_distinct_tmpdir.
  Hint Resolve proper_pathname_distinct_maildir.
  Hint Resolve proper_pathname_distinct_userdir.


  Lemma unique_dir_pn_ne : forall fs pn1 pn2 d1 d2,
    invariant fs ->
    path_eval_root fs pn1 (DirNode d1) ->
    path_eval_root fs pn2 (DirNode d2) ->
    pn1 <> pn2 ->
    d1 <> d2.
  Proof.
    unfold invariant; intuition idtac; subst.
    eapply H4 in H0.
    eapply H0 in H1.
    congruence.
  Qed.

  Lemma unique_dir_pn_eq : forall fs pn d1 d2,
    invariant fs ->
    path_eval_root fs pn (DirNode d1) ->
    path_eval_root fs pn (DirNode d2) ->
    d1 = d2.
  Proof.
    unfold invariant; intuition idtac; subst.
    eapply H in H0.
    eapply H0 in H1.
    congruence.
  Qed.

  Hint Resolve unique_dir_pn_ne.
  Hint Resolve unique_dir_pn_eq.

  Lemma maildir_ne_tmpdir : [maildir] <> [tmpdir].
  Proof.
    intro.
    inversion H.
  Qed.

  Lemma maildir_ne_maildir_user : forall user,
    [maildir] <> [maildir; user].
  Proof.
    congruence.
  Qed.

  Lemma tmpdir_ne_maildir_user : forall user,
    [tmpdir] <> [maildir; user].
  Proof.
    congruence.
  Qed.

  Lemma maildir_user_ne_maildir_user : forall user1 user2,
    user1 <> user2 ->
    [maildir; user1] <> [maildir; user2].
  Proof.
    congruence.
  Qed.

  Hint Resolve maildir_ne_tmpdir.
  Hint Resolve maildir_ne_maildir_user.
  Hint Resolve tmpdir_ne_maildir_user.
  Hint Resolve maildir_user_ne_maildir_user.


  Lemma link_lookup_right_mover : forall dirnum name,
    right_mover MailLinkAPI.step (LinkLookup dirnum name).
  Proof.
    unfold right_mover; intros.
    exists s1.
    inversion H0; clear H0; intuition idtac.
    - inversion H2; clear H2; subst; repeat sigT_eq; eauto.
    - inversion H0; clear H0; subst; repeat sigT_eq.
      + (* MailAllowLinkLookupRoot *)
        inversion H2; clear H2; subst; repeat sigT_eq.
        * (* lookup failed *)
          repeat ( step_inv; intuition idtac ).
          par: eauto 10.

         -- econstructor; eauto.
            econstructor.
            contradict H10; deex. eauto.
         -- econstructor; eauto.
            econstructor.
            contradict H10; deex. eauto.
         -- econstructor; eauto.
            econstructor.
            contradict H10; deex. eauto.
         -- econstructor; eauto.
            econstructor.
            contradict H10; deex. eauto.

        * (* lookup succeeded *)
          repeat ( step_inv; intuition idtac ).
          par: eauto 10.

      + (* MailAllowLinkLookupTmp *)
        inversion H2; clear H2; subst; repeat sigT_eq.
        * (* lookup failed *)
          repeat ( step_inv; intuition idtac ).
          all: eauto 6.

         -- econstructor; eauto.
            econstructor.
            contradict H12; deex. eauto.

         -- econstructor; eauto.
            econstructor.
            contradict H12; deex. eauto.

         -- econstructor; eauto.
            econstructor.
            contradict H12; deex. eauto.

         -- econstructor; eauto.
            econstructor.
            contradict H12; deex. eauto.

        * (* lookup succeeded *)
          repeat ( step_inv; intuition idtac ).
          par: eauto 10.

      + (* MailAllowLinkLookupMail *)
        inversion H2; clear H2; subst; repeat sigT_eq.
        * (* lookup failed *)
          repeat ( step_inv; intuition idtac ).
          all: eauto 6.

         -- econstructor; eauto.
            econstructor.
            contradict H11; deex. eauto.

         -- econstructor; eauto.
            econstructor.
            contradict H11; deex. eauto.

         -- econstructor; eauto.
            econstructor.
            contradict H11; deex. eauto.

         -- econstructor; eauto.
            econstructor.
            contradict H11; deex. eauto.

        * (* lookup succeeded *)
          repeat ( step_inv; intuition idtac ).
          par: eauto 10.

      + (* MailAllowLinkLookupUser *)
        inversion H2; clear H2; subst; repeat sigT_eq.
        * (* lookup failed *)
          repeat ( step_inv; intuition idtac ).
          all: eauto 15.

        * (* lookup succeeded *)
          repeat ( step_inv; intuition idtac ).
          par: eauto 15.

          destruct (user0 == user); subst.
         -- assert (dirnum0 = dirnum) by ( eapply unique_dir_pn_eq; eauto ).
            subst.

            assert (name <> name0).
            contradict H17; subst; eauto.
            eauto 20.

         -- assert (dirnum0 <> dirnum) by ( eapply unique_dir_pn_ne; eauto ).
            eauto 20.
  Qed.

  Ltac atomic_exec_inv_with_options :=
    match goal with
    | H : atomic_exec _ (match ?r with _ => _ end) _ _ _ _ _ |- _ =>
      destruct r
    | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
      idtac H;
      inversion H; clear H; subst; repeat maybe_proc_inv
    | H : Some _ = Some _ |- _ =>
      inversion H; clear H; subst
    end;
    autorewrite with t in *;
    try congruence.

  Ltac apply_in_atomic_exec H :=
    match goal with
    | Ha : atomic_exec _ _ _ _ _ _ _ |- _ =>
      apply H in Ha
    end.

  Lemma namei_spec_path_evaluates_some :
    forall n fs cwd pn tid r fs' evs,
    atomic_exec MailLinkAPI.step (namei_spec n cwd pn) tid fs (Some r) fs' evs ->
      evs = [] /\
      fs' = fs /\
      path_evaluates fs cwd pn r.
  Proof.
    induction n; intros; simpl in *.
    - repeat atomic_exec_inv_with_options.
    - repeat ( apply_in_atomic_exec IHn ||
               atomic_exec_inv_with_options ||
               step_inv ||
               congruence ).
      eauto.
      all: intuition idtac; subst; simpl; try congruence.
      all: eauto with model.
      inversion H5; subst.
      eauto.
  Qed.

  Lemma namei_spec_path_evaluates_none :
    forall n fs cwd pn tid fs' evs,
    atomic_exec MailLinkAPI.step (namei_spec n cwd pn) tid fs None fs' evs ->
      evs = [] /\
      fs' = fs.
  Proof.
    induction n; intros; simpl in *.
    - repeat atomic_exec_inv_with_options.
      eauto.
    - repeat ( apply_in_atomic_exec IHn ||
               apply_in_atomic_exec namei_spec_path_evaluates_some ||
               atomic_exec_inv_with_options ||
               step_inv ||
               congruence ).
      eauto.
      all: intuition idtac; subst; simpl; try congruence.
  Qed.

  Opaque namei_spec.

  Lemma namei_cwd_dir_path_evaluates_some :
    forall fs cwd pn tid r fs' evs,
    atomic_exec MailLinkAPI.step (namei_cwd_dir cwd pn) tid fs (Some r) fs' evs ->
      evs = [] /\
      fs' = fs /\
      path_evaluates fs (DirNode cwd) pn (DirNode r).
  Proof.
    intros.
    repeat ( apply_in_atomic_exec namei_spec_path_evaluates_some ||
             apply_in_atomic_exec namei_spec_path_evaluates_none ||
             atomic_exec_inv_with_options ||
             step_inv ||
             congruence ).
    rewrite app_nil_r.
    intuition eauto.
  Qed.

  Lemma namei_cwd_dir_path_evaluates_none :
    forall fs cwd pn tid fs' evs,
    atomic_exec MailLinkAPI.step (namei_cwd_dir cwd pn) tid fs None fs' evs ->
      evs = [] /\
      fs' = fs.
  Proof.
    intros.
    repeat ( apply_in_atomic_exec namei_spec_path_evaluates_some ||
             apply_in_atomic_exec namei_spec_path_evaluates_none ||
             atomic_exec_inv_with_options ||
             step_inv ||
             congruence ).
    all: rewrite app_nil_r.
    all: intuition eauto.
  Qed.

  Lemma namei_cwd_file_path_evaluates_some :
    forall fs cwd pn tid r fs' evs,
    atomic_exec MailLinkAPI.step (namei_cwd_file cwd pn) tid fs (Some r) fs' evs ->
      evs = [] /\
      fs' = fs /\
      path_evaluates fs (DirNode cwd) pn (FileNode r).
  Proof.
    intros.
    repeat ( apply_in_atomic_exec namei_spec_path_evaluates_some ||
             apply_in_atomic_exec namei_spec_path_evaluates_none ||
             atomic_exec_inv_with_options ||
             step_inv ||
             congruence ).
    rewrite app_nil_r.
    intuition eauto.
  Qed.

  Lemma namei_cwd_file_path_evaluates_none :
    forall fs cwd pn tid fs' evs,
    atomic_exec MailLinkAPI.step (namei_cwd_file cwd pn) tid fs None fs' evs ->
      evs = [] /\
      fs' = fs.
  Proof.
    intros.
    repeat ( apply_in_atomic_exec namei_spec_path_evaluates_some ||
             apply_in_atomic_exec namei_spec_path_evaluates_none ||
             atomic_exec_inv_with_options ||
             step_inv ||
             congruence ).
    all: rewrite app_nil_r.
    all: intuition eauto.
  Qed.

  Lemma read_files_ok :
    forall files fs cwd dir tid fs' evs r,
    atomic_exec MailLinkAPI.step (read_files cwd dir files) tid fs r fs' evs ->
      evs = [] /\
      fs' = fs /\
      match r with
      | Some msgs =>
        Forall2 (fun fn msg =>
          exists f,
            path_evaluates fs (DirNode cwd) (dir ++ [fn]) (FileNode f) /\
            nth_error (FSFiles fs) f = Some msg) files msgs
      | None => True
      end.
  Proof.
    induction files; intros; simpl in *.
    - repeat atomic_exec_inv_with_options.
      eauto.
    - repeat ( unfold message in * ||
               apply_in_atomic_exec IHfiles ||
               apply_in_atomic_exec namei_spec_path_evaluates_some ||
               apply_in_atomic_exec namei_spec_path_evaluates_none ||
               atomic_exec_inv_with_options ||
               step_inv ||
               congruence ).
      all: intuition subst; eauto.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op MailLinkAPI.step MailServerLinkAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    - do 40 ( step_inv ||
               rewrite app_nil_r ||
               rewrite app_nil_l ||
               solve [ intuition subst; eauto ] ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_none ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_none ||
               apply_in_atomic_exec namei_spec_path_evaluates_some ||
               apply_in_atomic_exec namei_spec_path_evaluates_none ||
               atomic_exec_inv_with_options ).

do 40 ( step_inv ||
               rewrite app_nil_r ||
               rewrite app_nil_l ||
               solve [ intuition subst; eauto ] ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_none ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_none ||
               apply_in_atomic_exec namei_spec_path_evaluates_some ||
               apply_in_atomic_exec namei_spec_path_evaluates_none ||
               atomic_exec_inv_with_options ).

repeat ( step_inv ||
               rewrite app_nil_r ||
               rewrite app_nil_l ||
               solve [ intuition subst; eauto ] ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_none ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_none ||
               apply_in_atomic_exec namei_spec_path_evaluates_some ||
               apply_in_atomic_exec namei_spec_path_evaluates_none ||
               atomic_exec_inv_with_options ).

intuition subst. eauto.
replace n1 with n2 in *.
exfalso; eauto.
replace (FSRoot s2) with (FSRoot (upd_file n3 m (add_link n4 (FileNode n) v3 s2))) in *.
eapply unique_dir_pn_eq.
2: unfold path_eval_root; eauto.
2: unfold path_eval_root; eauto.
eauto.
reflexivity.



repeat ( step_inv ||
               rewrite app_nil_r ||
               rewrite app_nil_l ||
               solve [ intuition subst; eauto ] ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_none ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_none ||
               apply_in_atomic_exec namei_spec_path_evaluates_some ||
               apply_in_atomic_exec namei_spec_path_evaluates_none ||
               atomic_exec_inv_with_options ).

repeat ( step_inv ||
               rewrite app_nil_r ||
               rewrite app_nil_l ||
               solve [ intuition subst; eauto ] ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_dir_path_evaluates_none ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_some ||
               apply_in_atomic_exec namei_cwd_file_path_evaluates_none ||
               apply_in_atomic_exec namei_spec_path_evaluates_some ||
               apply_in_atomic_exec namei_spec_path_evaluates_none ||
               atomic_exec_inv_with_options ).

intuition subst. eauto.
econstructor.
admit.
admit.
admit.
eauto.
eauto.
unfold create_file_write.
admit.

Search user.
Search path_evaluates add_link.
exfalso; eauto.
replace (FSRoot s2) with (FSRoot (upd_file n3 m (add_link n4 (FileNode n) v3 s2))) in *.
eapply unique_dir_pn_eq.
2: unfold path_eval_root; eauto.
2: unfold path_eval_root; eauto.
eauto.
reflexivity.


econstructor.
Search path_evaluates user.


Search n2.

Focus 12.

repeat ( step_inv ||
               rewrite app_nil_r ||
               rewrite app_nil_l ||
               solve [ intuition subst; eauto ] ||
               apply_in_atomic_exec namei_spec_path_evaluates_some ||
               apply_in_atomic_exec namei_spec_path_evaluates_none ||
               atomic_exec_inv_with_options ).
*)
    - repeat ( step_inv ||
               rewrite app_nil_r ||
               rewrite app_nil_l ||
               solve [ intuition subst; eauto ] ||
               apply_in_atomic_exec read_files_ok ||
               apply_in_atomic_exec namei_spec_path_evaluates_some ||
               apply_in_atomic_exec namei_spec_path_evaluates_none ||
               atomic_exec_inv_with_options ).

      intuition subst; eauto.
      destruct v.
      + econstructor; intros.
        split; intros.
        * generalize dependent (readdir_names s1 dirnum).
          induction l; intros. inversion H.
          inversion H8; clear H8. deex.
          inversion H; clear H; subst.
         -- do 2 eexists. unfold path_eval_root. simpl in *.
            eauto.
         -- eauto.
        * repeat deex.
          admit.
      + eauto.
  Admitted.


Hint Constructors mailfs_step_allowed.

Axiom tmpdir_not_maildir : forall user, tmpdir = (maildir ++ [user])%list -> False.
Hint Resolve tmpdir_not_maildir.


Hint Resolve starts_with_tid_ne.

Instance invariant_proper :
  Proper (FSEquiv ==> iff) invariant.
Proof.
  intros ? ? ?; subst.
  unfold invariant, unique_pathname_root; intuition idtac; repeat deex.
  - exists node.
    rewrite <- H in *.
    split; auto.
    intros.
    rewrite <- H in *.
    auto.
  - eexists node.
    rewrite H in *.
    split; auto.
    intros.
    rewrite H in *; auto.
Qed.

Lemma path_eval_root_create: forall fs pn dirnum h name,
    does_not_exist fs dirnum name ->
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root (create_file dirnum h name fs) pn (DirNode dirnum ).
Proof.
  intros.
  eapply path_eval_root_upd_file in H0.
  eapply path_eval_root_add_link in H0; eauto.
Qed.

(*
Lemma FS_path_evaluates_eq: forall fs fs' startdir pn node node',
    FSEquiv fs fs' ->
    path_evaluates fs (DirNode startdir) pn node ->
    path_evaluates fs' (DirNode startdir) pn node' ->
    node = node'.
Admitted.

Require Import Bool.
Require Import Ascii.

Definition eq_ascii (a1 a2 : ascii) :=
  match a1, a2 with
  | Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
    (eqb b1 c1) && (eqb b2 c2) && (eqb b3 c3) && (eqb b4 c4) &&
    (eqb b5 c5) && (eqb b6 c6) && (eqb b7 c7) && (eqb b8 c8)
  end.

Fixpoint eq_string (s1 s2 : string) :=
  match s1, s2 with
  | EmptyString,  EmptyString  => true
  | String x1 s1, String x2 s2 => eq_ascii x1 x2 && eq_string s1 s2
  | _, _                       => false
  end.

Definition match_dirent from s l :=
  eq_string s (LinkName l) && (beq_nat from (LinkFrom l)).

Definition dirents fs from name :=
  Graph.filter (match_dirent from name) fs.

Definition chooseone dirents := Graph.choose dirents.

Fixpoint path pn (fs:Graph.t) dir: Graph.t :=
  match pn with
  | nil => Graph.empty
  | e :: pn' =>
    let s := dirents fs dir e in
    match chooseone s with
    | None => Graph.empty
    | Some l =>
      match (LinkTo l) with
      | DirNode n => Graph.add l (path pn' fs n)
        (* XXX symbolic links *)                      
      | _ => Graph.empty
      end
    end
  end.
 *)

Lemma path_unique_eq: forall fs dirnum pn node',
    unique_pathname_root fs pn ->
    path_eval_root fs pn (DirNode dirnum) ->
    path_eval_root fs pn node' ->
    node' = DirNode dirnum.
Proof.
  intros.
  unfold unique_pathname_root in *.
  deex.
  specialize (H2 (DirNode dirnum)) as Hx.
  specialize (Hx H0).
  subst.
  specialize (H2 node' H1); auto.
Qed.

Lemma path_unique_create_inum_eq: forall fs pn dirnum dirnum0 h name,
    unique_pathname_root fs pn ->
    does_not_exist fs dirnum0 name ->
    file_handle_unused fs h ->
    file_handle_valid fs h ->
    unique_pathname_root (create_file dirnum0 h name fs) pn ->
    path_eval_root fs pn (DirNode dirnum0) ->
    path_eval_root (create_file dirnum0 h name fs) pn (DirNode dirnum) ->
    dirnum = dirnum0.
Proof.
  intros.
  assert (DirNode dirnum = DirNode dirnum0) as Hinum.
  eapply path_eval_root_create in H4 as Hx; try eassumption.
  eapply path_unique_eq in H3; try eassumption.
  inversion Hinum; auto.
Qed.

Lemma path_evaluates_add_link_upd_file : forall fs startdir node h data dirpn from to name,
    path_evaluates (add_link from to name fs) startdir dirpn node ->
    path_evaluates (add_link from to name (upd_file h data fs)) startdir dirpn node.
Proof.
  intros.
  remember (add_link from to name fs).
  generalize dependent fs; intros.
  induction H.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; subst; simpl.
    inversion H; subst; clear H.
    constructor; simpl; eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_add_link_upd_file' : forall fs startdir node h data dirpn from to name,
    path_evaluates (add_link from to name (upd_file h data fs)) startdir dirpn node ->
    path_evaluates (add_link from to name fs) startdir dirpn node.
Proof.
  intros.
  remember (add_link from to name (upd_file h data fs)).
  generalize dependent fs; intros.
  induction H.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; subst; simpl.
    inversion H; subst; clear H.
    constructor; simpl; eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_add_link_comm: forall fs pn startdir dirnum0 name2 n1 name1 n2 node,
    path_evaluates (add_link dirnum0 n1 name1 (add_link dirnum0 n2 name2 fs)) (DirNode startdir) pn node ->
    path_evaluates (add_link dirnum0 n2 name2 (add_link dirnum0 n1 name1 fs)) (DirNode startdir) pn node.
Proof.
  intros.
  remember ((add_link dirnum0 n1 name1 (add_link dirnum0 n2 name2 fs))).
  generalize dependent fs; intros.
  induction H; subst.
  + constructor.
  + apply PathEvalFileLink; subst.
    inversion H; subst; clear H.
    constructor; simpl in *.
    apply In_add_add_comm; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; auto.
      apply In_add_add_comm; auto.
    - apply ValidDot.
    - eapply ValidDotDot.
      apply In_add_add_comm; eauto.
    - apply ValidDotDotRoot; auto.
  + inversion H; subst.
    eapply PathEvalSymlink; simpl.
    - constructor; simpl in *.
      apply In_add_add_comm; auto.
      apply H2.
    - apply IHpath_evaluates1; eauto.
    - apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_add_link_add_link_upd_file: forall fs startdir dirnum0 node node0 node1 name0 name1 h data pn,
   path_evaluates
        (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 (upd_file h data fs))) startdir pn node ->
   path_evaluates
     (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 fs)) startdir pn node.
Proof.
  intros.
  remember (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 (upd_file h data fs))).
  generalize dependent fs; intros.
  induction H; subst.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; subst; simpl.
    inversion H; subst; clear H.
    constructor; simpl; eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_add_link_add_link_upd_file': forall fs startdir dirnum0 node node0 node1 name0 name1 h data pn,
   path_evaluates
     (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 fs)) startdir pn node ->
   path_evaluates
        (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 (upd_file h data fs))) startdir pn node.
Proof.
  intros.
  remember (add_link dirnum0 node0 name0 (add_link dirnum0 node1 name1 fs)).
  generalize dependent fs; intros.
  induction H; subst.
  + constructor.
  + eapply PathEvalFileLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
  + eapply PathEvalDirLink; eauto.
    inversion H; subst; clear H.
    - constructor; simpl; auto.
    - apply ValidDot.
    - eapply ValidDotDot; simpl; eauto.
    - apply ValidDotDotRoot; auto.
  + eapply PathEvalSymlink; subst; simpl.
    inversion H; subst; clear H.
    constructor; simpl; eauto.
    apply IHpath_evaluates1; eauto.
    apply IHpath_evaluates2; eauto.
Qed.

Lemma path_evaluates_create_comm: forall fs pn startdir dirnum0 name0 v0 name1 v1 node,
    path_evaluates (create_file dirnum0 v0 name0 (create_file dirnum0 v1 name1 fs)) (DirNode startdir) pn node ->
    path_evaluates (create_file dirnum0 v1 name1 (create_file dirnum0 v0 name0 fs)) (DirNode startdir) pn node.
Proof.
  intros.
  unfold create_file in *.
  simpl in *.
  eapply path_evaluates_add_link_upd_file.
  eapply path_evaluates_add_link_upd_file' in H.
  eapply path_evaluates_add_link_add_link_upd_file in H.
  eapply path_evaluates_add_link_add_link_upd_file'.
  apply path_evaluates_add_link_comm; auto.
Qed.

Lemma path_eval_root_create_comm: forall fs pn dirnum0 name v0 name0 v1 node,
    path_eval_root (create_file dirnum0 v1 name0 (create_file dirnum0 v0 name fs)) pn node ->
    path_eval_root (create_file dirnum0 v0 name (create_file dirnum0 v1 name0 fs)) pn node.
Proof.
  intros.
  unfold path_eval_root in *.
  eapply path_evaluates_create_comm; eauto.
Qed.

Lemma unique_pathname_create_comm: forall fs pn dirnum0 name v0 name0 v1,
    unique_pathname_root (create_file dirnum0 v1 name0 (create_file dirnum0 v0 name fs)) pn ->
    unique_pathname_root (create_file dirnum0 v0 name (create_file dirnum0 v1 name0 fs)) pn.
Proof.
  intros.
  unfold unique_pathname_root in H.
  unfold unique_pathname_root.
  deex.
  exists node.
  split; auto.
  eapply path_evaluates_create_comm; try eassumption.
  intros.
  specialize (H0 node'); auto.
  edestruct H0.
  eapply path_evaluates_create_comm; try eassumption.
  reflexivity.
Qed.  

Lemma invariant_create_comm: forall fs dirnum0 name v0 name0 v1,
    invariant (create_file dirnum0 v1 name0 (create_file dirnum0 v0 name fs)) ->
    invariant (create_file dirnum0 v0 name (create_file dirnum0 v1 name0 fs)).
Proof.
  intros.
  unfold invariant in *.
  eapply unique_pathname_create_comm; eauto.
Qed.

Lemma unique_pathname_create: forall fs pn dirnum name1 v1,
    unique_pathname_root fs pn ->
    path_eval_root fs pn (DirNode dirnum) ->
    unique_pathname_root (create_file dirnum v1 name1 fs) pn.
Proof.
  intros.
  unfold unique_pathname_root, unique_pathname in *.
  repeat deex.
  unfold create_file, path_eval_root in *.
  eexists.
  split.
  eapply path_evaluates_add_link_upd_file; simpl.
  eapply path_evaluates_add_link in H as Hx.
  apply Hx.

  intros.
  eapply H1.
  eapply path_evaluates_add_link_upd_file' in H2.
  simpl in *.
  apply path_evaluates_add_link' in H2; simpl in *; eauto.
  unfold unique_pathname.
  eexists.
  split; eauto.
  intros.
  specialize (H1 node'0 H3) as H1x; subst.
  symmetry.
  specialize (H1 (DirNode dirnum) H0) as H1x; subst; auto.
Admitted.

Lemma invariant_create: forall fs dirnum name1 v1,
    path_eval_root fs tmpdir (DirNode dirnum) ->
    invariant fs ->
    invariant (create_file dirnum v1 name1 fs).
Proof.
  intros.
  unfold invariant in *.
  eapply unique_pathname_create; eauto.
Qed.

Lemma fsequiv_create_file_comm: forall fs dirnum h0 h1 name1 name0,
    file_handle_unused fs h0 ->
    file_handle_unused (create_file dirnum h0 name0 fs) h1 ->
    FSEquiv (create_file dirnum h1 name1 (create_file dirnum h0 name0 fs))
            (create_file dirnum h0 name0 (create_file dirnum h1 name1 fs)).
Proof.
  intros.
  unfold create_file, FSEquiv; simpl.
  destruct fs; simpl.
  intuition eauto.
  eapply list_upd_commutes.
  eapply file_handle_unused_ne in H0 as Hx; eauto.
  unfold Graph.Equal; split; intros.
  eapply In_add_add_comm; eauto.
  eapply In_add_add_comm; eauto.
Qed.

Theorem create_tmpdir_both_mover : forall dir name,
  both_mover mailfs_step (Create dir name).
Proof.
  split; intros.
  - unfold right_mover; intros.
    repeat step_inv; unfold mailfs_step; intuition eauto; simpl in *.
    repeat step_inv.
    repeat subst_fsequiv.

    replace dirnum with dirnum0 in *.
    2: eapply path_unique_create_inum_eq in H7 as Hi; auto.

    eexists; split; subst_fsequiv.
    + intuition idtac.
      econstructor; eauto.
      2: reflexivity; eauto.
      econstructor; eauto.
      eauto.

      eapply invariant_create; eauto.
      
      (* eapply invariant_create_comm in H11 as H11x; eauto. *)
        
      (* some come from econstructor; others form invariant_create *)
      Unshelve.
      all: auto.

    + intuition idtac.
      econstructor.
      econstructor.

      eapply path_eval_root_create in H8 as H8x.
      apply H8x.

      eauto.
      all: try unfold create_file; eauto.

      apply fsequiv_create_file_comm; auto.
      eapply invariant_create_comm in H11 as H11x; eauto.
      eapply invariant_create; eauto.
      Unshelve.
      all: auto.

  - admit.
Admitted.

*)
