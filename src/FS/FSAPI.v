Require Import POCS.


Import ListNotations.
Require Import String.
Require Import FS.SepLogic.Mem.
Require Import FS.SepLogic.Pred.


Record file := mk_file {
  FileData : string;
}.

Definition empty_file := 
  mk_file "".

Inductive tree_node :=
| Missing
| Dir : forall (inum : nat), tree_node
| File : forall (handle : nat) (f : file), tree_node.

Definition pathname := list string.


Definition State := mem pathname tree_node.

(* One interesting difference from FSCQ's DirSep: the memory contains
  [Some Missing] entries for files that do not exist in an existing directory,
  but the memory contains [None] for entries in non-existant directories,
  children of files, etc.
*)

Definition empty_dir : pred pathname tree_node :=
  mkPred (fun m => forall fn, m [fn] = Some Missing).

Axiom pathname_decide_prefix : forall (base pn : pathname),
  { suffix | pn = base ++ suffix } +
  { ~ exists suffix, pn = base ++ suffix }.

Definition subtree_pred (dirname : pathname)
                        (p : pred pathname tree_node) : pred pathname tree_node :=
  mkPred (fun m =>
    exists (subm : mem pathname tree_node),
    subm |= p /\
    forall (pn : pathname),
    match pathname_decide_prefix dirname pn with
    | inleft (exist _ suffix _) => m pn = subm suffix
    | inright _ => m pn = None
    end).

Instance pathname_eq : EquivDec.EqDec pathname eq.
  intros a b.
  destruct (list_eq_dec string_dec a b).
  left. congruence.
  right. congruence.
Qed.


Definition maildir := ["/tmp/"%string; "mail/"%string].
Definition tmpdir := ["/tmp/"%string].

Global Opaque maildir.
Global Opaque tmpdir.


(*
Axiom fs_concur : forall (tid : string) (p : pred pathname tree_node), pred pathname tree_node.
Axiom fs_concur_star : forall tid p1 p2,
  fs_concur tid (p1 * p2) ===> fs_concur tid p1 * fs_concur tid p2.
Axiom fs_concur_dir : forall tid pn dirid,
  fs_concur tid (pn |-> Dir dirid) ===> pn |-> Dir dirid.
Axiom fs_concur_tmp1 : forall tid suffix handle f,
  fs_concur tid ((tmpdir ++ [(tid ++ "."%string ++ suffix)%string]%list) |-> File handle f) ===>
  (tmpdir ++ [(tid ++ "."%string ++ suffix)%string]%list) |-> File handle f.
Axiom fs_concur_tmp2 : forall tid suffix,
  fs_concur tid ((tmpdir ++ [(tid ++ "."%string ++ suffix)%string]%list) |-> Missing) ===>
  (tmpdir ++ [(tid ++ "."%string ++ suffix)%string]%list) |-> Missing.
Axiom fs_concur_maildir : forall tid user suffix,
  fs_concur tid ((maildir ++ [user] ++ [(tid ++ "."%string ++ suffix)%string]%list) |-> Missing) ===>
  (maildir ++ [user] ++ [(tid ++ "."%string ++ suffix)%string]%list) |-> Missing.
Axiom fs_concur_idem : forall tid p,
  fs_concur tid (fs_concur tid p) ===> fs_concur tid p.


Require Import Setoid Classes.Morphisms.

Global Instance fs_concur_proper : Proper (eq ==> pimpl ==> pimpl) fs_concur.
Admitted.

Global Instance subtree_pred_proper : Proper (eq ==> pimpl ==> pimpl) subtree_pred.
Admitted.

Lemma fs_concur_exists : forall tid T (p : T -> _),
  fs_concur tid (exists x, p x) ===> exists x, fs_concur tid (p x).
Admitted.
*)

Lemma subtree_pred_exists : forall pn T (p : T -> _),
  subtree_pred pn (exists x, p x) ===> exists x, subtree_pred pn (p x).
Admitted.

Lemma subtree_pred_star : forall pn p1 p2,
  subtree_pred pn (p1 * p2) ===> subtree_pred pn p1 * subtree_pred pn p2.
Admitted.

Lemma subtree_pred_ptsto : forall pn a v,
  subtree_pred pn (a |-> v) ===> (pn ++ a) |-> v.
Admitted.


Definition inited (s : State) : Prop :=
  s |= nil |-> Dir 0 * empty_dir.



Inductive stat_result :=
| StatMissing
| StatFile
| StatDir.

Inductive fsOpT : Type -> Type :=
| Create (dir : pathname) (name : string) : fsOpT nat
| Mkdir (dir : pathname) (name : string) : fsOpT nat
| Delete (pn : pathname) : fsOpT unit
| Rmdir (pn : pathname) : fsOpT unit
| Stat (dir : pathname) (name : string) : fsOpT stat_result
| Readdir (pn : pathname) : fsOpT (list string)
| Rename (src : pathname) (dstdir : pathname) (dstname : string) : fsOpT unit
| Read (pn : pathname) : fsOpT string
| Write (pn : pathname) (data : string) : fsOpT unit
| FindAvailableName (dir : pathname) : fsOpT string
| Debug (s : string) : fsOpT unit.


Definition frame_pre_post (s s' : State) (p p' : pred _ _) : Prop :=
  (exists F, s |= F * p) /\
  (forall F, s |= F * p <-> s' |= F * p').

Arguments frame_pre_post s s' (p p')%pred.

Parameter tid_to_string : nat -> string.

Definition starts_with_tid tid (name : string) : Prop :=
  exists namesuffix,
    name = (tid_to_string tid ++ "." ++ namesuffix)%string.


Inductive fs_step : forall T, fsOpT T -> nat -> State -> T -> State -> Prop :=
| StepCreate : forall dir name tid s h s' dirnum,
  frame_pre_post s s'
    (dir |-> Dir dirnum * (dir ++ [name]) |-> Missing)
    (dir |-> Dir dirnum * (dir ++ [name]) |-> File h empty_file) ->
  fs_step (Create dir name) tid s h s'

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
.


Inductive mailfs_step_allowed : forall T, fsOpT T -> nat -> Prop :=
| MailStepCreateTmp : forall dir name tid,
  dir = tmpdir ->
  starts_with_tid tid name ->
  mailfs_step_allowed (Create dir name) tid

| MailStepFindAvailableNameTmp : forall tid,
  mailfs_step_allowed (FindAvailableName tmpdir) tid

| MailStepFindAvailableNameUser : forall user dir tid,
  dir = maildir ++ [user] ->
  mailfs_step_allowed (FindAvailableName dir) tid

| MailStepWriteTmp : forall pn dir name tid data,
  dir = tmpdir ->
  starts_with_tid tid name ->
  pn = dir ++ [name] ->
  mailfs_step_allowed (Write pn data) tid

| MailStepRenameTmpToMailbox : forall src srcname dstdir user dstname tid,
  src = tmpdir ++ [srcname] ->
  starts_with_tid tid srcname ->
  dstdir = maildir ++ [user] ->
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
  _ <- Op (Write (tmpdir ++ [tmpname]) m);
  fn <- Op (FindAvailableName (maildir ++ [user]));
  _ <- Op (Rename (tmpdir ++ [tmpname]) (maildir ++ [user]) fn);
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

Ltac frame_inv :=
  match goal with
  | H : frame_pre_post _ _ _ _ |- _ =>
    destruct H; repeat deex
  end.

Hint Constructors fs_step.
Hint Constructors mailfs_step_allowed.

Axiom tmpdir_not_maildir : forall user, tmpdir = maildir ++ [user] -> False.
Hint Resolve tmpdir_not_maildir.


Theorem find_available_name_tmpdir_both_mover :
  both_mover mailfs_step (FindAvailableName tmpdir).
Proof.
  split; intros.
  - unfold right_mover; intros.
    exists s1.
    repeat step_inv; unfold mailfs_step; intuition eauto.
    all: try solve [ exfalso; eauto ].
    all: frame_inv.
    all: econstructor; eauto.
    + eapply pimpl_trans. reflexivity.
      2: eapply H2.
      instantiate (3 := (_ * (tmpdir ++ [v0]) |-> Missing)%pred).
      instantiate (2 := (_ * (tmpdir ++ [name]) |-> File v1 empty_file)%pred).
      norm. cancel. reflexivity.

      eapply pimpl_trans. reflexivity.
      2: eapply pred_extract_merge.
      2: eassumption.
      2: apply H0.

      repeat rewrite pred_eexcept_star.
      repeat rewrite pred_eexcept_ptsto_ne.
      norm. cancel. reflexivity.

      admit.
      admit.

    + eapply pimpl_trans. reflexivity.
      2: eapply H2.
      admit.
      admit.

    + admit.

  - admit.
Admitted.

Theorem create_tmpdir_both_mover : forall dir name,
  both_mover mailfs_step (Create dir name).
Proof.
  split; intros.
  - unfold right_mover; intros.
    repeat step_inv; unfold mailfs_step; intuition eauto.

    + exists (upd s (tmpdir ++ [name0]) (File v1 empty_file)).
      repeat frame_inv.

      eapply H2 in H0 as H0'.
      eapply pred_extract_merge with (a := tmpdir ++ [name]) in H3 as H3'.
      2: eapply pimpl_trans. 2: reflexivity. 3: eapply H0'.
      2: norm. 2: cancel. 2: unfold stars; simpl. 2: reflexivity.

      assert (Dir dirnum = Dir dirnum0).
      eapply pred_merge_eq with (a := tmpdir).
      eapply pimpl_trans. reflexivity. 2: eapply H3.
      norm. cancel. unfold stars; simpl. reflexivity.
      eapply pimpl_trans. reflexivity. 2: eapply H0'.
      norm. cancel. unfold stars; simpl. reflexivity.
      inversion H7; clear H7; subst.

      eapply pred_extract_merge with (a := tmpdir ++ [name0]) in H0 as H0''.
      2: eapply pimpl_trans. 2: reflexivity. 3: eapply H2.
      3: eapply pimpl_trans. 3: reflexivity. 4: eapply H3'.
      3: repeat rewrite pred_eexcept_star.
      3: repeat rewrite pred_eexcept_ptsto_ne.
      3: norm. 3: cancel. 3: unfold stars; simpl; reflexivity.
      2: norm. 2: cancel. 2: unfold stars; simpl; reflexivity.

Admitted.
