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


Module MailAtomic <: LayerImpl MailLinkAPI MailServerLinkAPI.

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


