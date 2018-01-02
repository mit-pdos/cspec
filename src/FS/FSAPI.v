Require Import POCS.


Import ListNotations.
Require Import String.
Require Import Trees.


Definition State := FS.

Definition maildir := ["/tmp/"%string; "mail/"%string].
Definition tmpdir := ["/tmp/"%string].

Global Opaque maildir.
Global Opaque tmpdir.


Inductive stat_result :=
| StatMissing
| StatFile
| StatDir.

Inductive fsOpT : Type -> Type :=
| Create (dir : Pathname) (name : string) : fsOpT nat
| Mkdir (dir : Pathname) (name : string) : fsOpT nat
| Delete (pn : Pathname) : fsOpT unit
| Rmdir (pn : Pathname) : fsOpT unit
| Stat (dir : Pathname) (name : string) : fsOpT stat_result
| Readdir (pn : Pathname) : fsOpT (list string)
| Rename (src : Pathname) (dstdir : Pathname) (dstname : string) : fsOpT unit
| Read (pn : Pathname) : fsOpT string
| Write (pn : Pathname) (data : string) : fsOpT unit
| FindAvailableName (dir : Pathname) : fsOpT string
| Debug (s : string) : fsOpT unit.


Parameter tid_to_string : nat -> string.

Definition starts_with_tid tid (name : string) : Prop :=
  exists namesuffix,
    name = (tid_to_string tid ++ "." ++ namesuffix)%string.


Inductive fs_step : forall T, fsOpT T -> nat -> State -> T -> State -> Prop :=
| StepCreate : forall dir name tid s h s' dirnum,
  path_eval_root s dir (DirNode dirnum) ->
  (~ exists n, Graph.In (mkLink dirnum n name) (FSLinks s)) ->
  (~ exists d name', Graph.In (mkLink d (FileNode h) name') (FSLinks s)) ->
  h < Datatypes.length (FSFiles s) ->
  s' = mkFS (FSRoot s)
            (Graph.add (mkLink dirnum (FileNode h) name) (FSLinks s))
            (list_upd (FSFiles s) h "") ->
  fs_step (Create dir name) tid s h s'

(*

| StepMkdir : forall dir name tid s h s' dirnum newdirnum,
  frame_pre_post s s'
    (dir |-> Dir dirnum * (dir ++ [name]) |-> Missing)
    (dir |-> Dir dirnum * (dir ++ [name]) |-> Dir newdirnum
                        * subtree_pred (dir ++ [name]) empty_dir) ->
  fs_step (Mkdir dir name) tid s h s'

| StepDelete : forall pn h f tid s s',
  frame_pre_post s s'
    (pn |-> File h f)
    (pn |-> Missing) ->
  fs_step (Delete pn) tid s tt s'

| StepRmdir : forall pn dirnum tid s s',
  frame_pre_post s s'
    (pn |-> Dir dirnum * subtree_pred pn empty_dir)
    (pn |-> Missing) ->
  fs_step (Rmdir pn) tid s tt s'

| StepStat : forall dir name tid s r F dirnum,
  s  |= F * dir |-> Dir dirnum ->
  (r = StatFile ->
    exists F' h f, F' * (dir ++ [name]) |-> File h f ===> F) ->
  (r = StatDir ->
    exists F' dirnum', F' * (dir ++ [name]) |-> Dir dirnum' ===> F) ->
  (r = StatMissing ->
    exists F', F' * (dir ++ [name]) |-> Missing ===> F) ->
  fs_step (Stat dir name) tid s r s

| StepReaddir : forall dir tid s r F dirnum,
  s  |= F * dir |-> Dir dirnum ->
  (forall fn,
    (In fn r /\ exists F' handle f,
     F' * (dir ++ [fn]) |-> File handle f ===> F) \/
    (In fn r /\ exists F' dirinum,
     F' * (dir ++ [fn]) |-> Dir dirinum ===> F) \/
    (~ In fn r /\ exists F',
     F' * (dir ++ [fn]) |-> Missing ===> F)) ->
  fs_step (Readdir dir) tid s r s

| StepRename : forall src dstdir dstname tid s handle f s' dirnum,
  frame_pre_post s s'
    (src |-> File handle f
          * dstdir |-> Dir dirnum
          * (dstdir ++ [dstname]) |-> Missing)
    (src |-> Missing
          * dstdir |-> Dir dirnum
          * (dstdir ++ [dstname]) |-> File handle f) ->
  fs_step (Rename src dstdir dstname) tid s tt s'

| StepRead : forall pn tid s r handle F,
  s  |= F * pn |-> File handle r ->
  fs_step (Read pn) tid s (FileData r) s

| StepWrite : forall pn tid s s' handle f0 data,
  frame_pre_post s s'
    (pn |-> File handle f0)
    (pn |-> File handle (mk_file data)) ->
  fs_step (Write pn data) tid s tt s'

| StepFindAvailableName : forall dir dirnum tid s name F,
  starts_with_tid tid name ->
  s  |= F * dir |-> Dir dirnum * (dir ++ [name]) |-> Missing ->
  fs_step (FindAvailableName dir) tid s name s

| StepDebug : forall msg tid s,
  fs_step (Debug msg) tid s tt s
*)
.


Inductive mailfs_step_allowed : forall T, fsOpT T -> nat -> Prop :=
| MailStepCreateTmp : forall dir name tid,
  dir = tmpdir ->
  starts_with_tid tid name ->
  mailfs_step_allowed (Create dir name) tid

| MailStepFindAvailableNameTmp : forall tid,
  mailfs_step_allowed (FindAvailableName tmpdir) tid

| MailStepFindAvailableNameUser : forall user dir tid,
  dir = (maildir ++ [user])%list ->
  mailfs_step_allowed (FindAvailableName dir) tid

| MailStepWriteTmp : forall pn dir name tid data,
  dir = tmpdir ->
  starts_with_tid tid name ->
  pn = (dir ++ [name])%list ->
  mailfs_step_allowed (Write pn data) tid

| MailStepRenameTmpToMailbox : forall src srcname dstdir user dstname tid,
  src = (tmpdir ++ [srcname])%list ->
  starts_with_tid tid srcname ->
  dstdir = (maildir ++ [user])%list ->
  starts_with_tid tid dstname ->
  mailfs_step_allowed (Rename src dstdir dstname) tid
.

Definition mailfs_step T (op : fsOpT T) tid s r s' :=
  fs_step op tid s r s' /\
  mailfs_step_allowed op tid.



Definition message := string.

Inductive mailT : Type -> Type :=
| Deliver (user : string) (m : message) : mailT unit.


Definition deliver_core (user : string) (m : message) : proc fsOpT mailT unit :=
  tmpname <- Op (FindAvailableName tmpdir);
  _ <- Op (Create tmpdir tmpname);
  _ <- Op (Write (tmpdir ++ [tmpname])%list m);
  fn <- Op (FindAvailableName (maildir ++ [user])%list);
  _ <- Op (Rename (tmpdir ++ [tmpname])%list (maildir ++ [user])%list fn);
  Ret tt.


Ltac step_inv :=
  match goal with
  | H : fs_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : mailfs_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : mailfs_step_allowed _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.

Hint Constructors fs_step.
Hint Constructors mailfs_step_allowed.

Axiom tmpdir_not_maildir : forall user, tmpdir = (maildir ++ [user])%list -> False.
Hint Resolve tmpdir_not_maildir.

Axiom starts_with_tid_ne : forall tid0 tid1 name0 name1,
  tid0 <> tid1 ->
  starts_with_tid tid0 name0 ->
  starts_with_tid tid1 name1 ->
  name0 <> name1.



Lemma path_eval_root_0 : forall fs dirnum name dirpn n files' dirnum',
  path_eval_root fs dirpn (DirNode dirnum) ->
  (~ exists n, Graph.In (mkLink dirnum n name) (FSLinks fs)) ->
  path_eval_root (mkFS (FSRoot fs)
                       (Graph.add (mkLink dirnum n name) (FSLinks fs))
                       files') dirpn (DirNode dirnum') ->
  dirnum = dirnum'.
Admitted.

Lemma path_eval_root_1 : forall fs dirnum name dirpn n files',
  path_eval_root fs dirpn (DirNode dirnum) ->
  (~ exists n, Graph.In (mkLink dirnum n name) (FSLinks fs)) ->
  path_eval_root (mkFS (FSRoot fs)
                       (Graph.add (mkLink dirnum n name) (FSLinks fs))
                       files') dirpn (DirNode dirnum).
Admitted.


Theorem create_tmpdir_both_mover : forall dir name,
  both_mover mailfs_step (Create dir name).
Proof.
  split; intros.
  - unfold right_mover; intros.
    repeat step_inv; unfold mailfs_step; intuition eauto; simpl in *.
    eapply path_eval_root_0 in H7 as H7'; eauto; subst.

    eexists; intuition eauto.
    + econstructor.
      * eauto.
      * intro; repeat deex.
        destruct H9. exists n.
        apply Graph.add_spec; right; auto.
      * intro; repeat deex; eauto.
        destruct H12. exists d, name'.
        apply Graph.add_spec; right; auto.
      * admit.
      * reflexivity.

    + simpl in *.
      econstructor.
      * eapply path_eval_root_1; eauto.
        intro; repeat deex; eauto.
        destruct H9. exists n.
        apply Graph.add_spec; right; auto.
      * intro; repeat deex; eauto.
        simpl in *. intuition eauto.
        apply Graph.add_spec in H0.
        intuition idtac.
        inversion H2; subst.
        eapply starts_with_tid_ne; eauto.
        destruct H11.
        exists n; eauto.
      * intro; repeat deex; eauto.
        simpl in *. intuition eauto.
        (* same as above *)
        admit.
      * admit.
      * simpl.
        f_equal.
        (* XXX these sets are semantically the same ... *)
        rewrite Graph.equal_spec.
        admit. (* should be sets, not lists *)
        (* XXX FSFiles should be a set too ... *)
        admit.

  - admit.
Admitted.
