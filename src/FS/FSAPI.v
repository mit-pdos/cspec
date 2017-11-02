Require Import POCS.


Import ListNotations.
Require Import String.
Require Import FS.SepLogic.Mem.
Require Import FS.SepLogic.Pred.


Definition pointed_set (T : Type) : Type := T * list T.

Definition set_add {T} (s : pointed_set T) (v : T) := (v, fst s :: snd s).

Definition set_latest {T} (s : pointed_set T) := fst s.

Definition set_older {T} (s : pointed_set T) := snd s.

Definition set_transform {T} (s s' : pointed_set T) (rel : T -> T -> Prop) :=
  rel (fst s) (fst s') /\
  Forall2 rel (snd s) (snd s').

Definition set_in {T} (v : T) (s : pointed_set T) :=
  v = fst s \/
  In v (snd s).


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


Definition State := pointed_set (mem pathname tree_node).

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


Require Import Setoid Classes.Morphisms.

Global Instance fs_concur_proper : Proper (eq ==> pimpl ==> pimpl) fs_concur.
Admitted.

Global Instance subtree_pred_proper : Proper (eq ==> pimpl ==> pimpl) subtree_pred.
Admitted.

Lemma fs_concur_exists : forall tid T (p : T -> _),
  fs_concur tid (exists x, p x) ===> exists x, fs_concur tid (p x).
Admitted.

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
  set_older s = nil /\
  set_latest s |= nil |-> Dir 0 * empty_dir.

Definition create_spec tid dir name : Specification _ _ unit State :=
  fun '(F, dirnum) state => {|
    pre :=
      set_latest state |= F * dir |-> Dir dirnum * (dir ++ [name]) |-> Missing;
    post := fun r state' =>
      exists handle m,
      r = handle /\
      m |= fs_concur tid (F * dir |-> Dir dirnum * (dir ++ [name]) |-> File handle empty_file) /\
      (forall mold,
       set_in mold state ->
       ~ exists F' pn f', mold |= F' * pn |-> File handle f') /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Definition mkdir_spec tid dir name : Specification _ _ unit State :=
  fun '(F, dirnum) state => {|
    pre :=
      set_latest state |= F * dir |-> Dir dirnum * (dir ++ [name]) |-> Missing;
    post := fun r state' =>
      exists newdirnum m,
      r = newdirnum /\
      m |= fs_concur tid (F * dir |-> Dir dirnum * (dir ++ [name]) |-> Dir newdirnum *
           subtree_pred (dir ++ [name]) empty_dir) /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Definition delete_spec tid pn : Specification _ _ unit State :=
  fun '(F, handle, f) state => {|
    pre :=
      set_latest state |= F * pn |-> File handle f;
    post := fun r state' =>
      exists m,
      r = tt /\
      m |= fs_concur tid (F * pn |-> Missing) /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Definition rmdir_spec tid pn : Specification _ _ unit State :=
  fun '(F, dirnum) state => {|
    pre :=
      set_latest state |= F * pn |-> Dir dirnum * subtree_pred pn empty_dir;
    post := fun r state' =>
      exists m,
      r = tt /\
      m |= fs_concur tid (F * pn |-> Missing) /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Inductive stat_result :=
| StatMissing
| StatFile
| StatDir.

Definition stat_spec dirpn name : Specification _ _ unit State :=
  fun '(F, dirnum) state => {|
    pre :=
      set_latest state |= F * dirpn |-> Dir dirnum;
    post := fun r state' =>
      state' = state /\
      ((r = StatFile /\ exists F' handle f,
        F' * (dirpn ++ [name]) |-> File handle f ===> F) \/
       (r = StatDir /\ exists F' dirinum,
        F' * (dirpn ++ [name]) |-> Dir dirinum ===> F) \/
       (r = StatMissing /\ exists F',
        F' * (dirpn ++ [name]) |-> Missing ===> F));
    recovered := fun _ _ => False
  |}.

Definition readdir_spec dirpn : Specification _ _ unit State :=
  fun '(F, dirnum) state => {|
    pre :=
      set_latest state |= F * dirpn |-> Dir dirnum;
    post := fun r state' =>
      state' = state /\
      forall fn,
      ((In fn r /\ exists F' handle f,
        F' * (dirpn ++ [fn]) |-> File handle f ===> F) \/
       (In fn r /\ exists F' dirinum,
        F' * (dirpn ++ [fn]) |-> Dir dirinum ===> F) \/
       (~ In fn r /\ exists F',
        F' * (dirpn ++ [fn]) |-> Missing ===> F));
    recovered := fun _ _ => False
  |}.

Definition rename_file_spec pn dstdir dstname : Specification _ _ unit State :=
  fun '(F, handle, f, dirnum) state => {|
    pre :=
      set_latest state |= F * pn |-> File handle f *
               dstdir |-> Dir dirnum * (dstdir ++ [dstname]) |-> Missing;
    post := fun r state' =>
      exists m,
      r = tt /\
      m |= F * pn |-> Missing *
           dstdir |-> Dir dirnum * (dstdir ++ [dstname]) |-> File handle f /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Definition read_spec pn : Specification _ _ unit State :=
  fun '(F, handle, f) state => {|
    pre :=
      set_latest state |= F * pn |-> File handle f;
    post := fun r state' =>
      r = FileData f /\
      state' = state;
    recovered := fun _ _ => False
  |}.

Definition write_logged_spec pn data : Specification _ _ unit State :=
  fun '(F, handle, f0) state => {|
    pre :=
      set_latest state |= F * pn |-> File handle f0;
    post := fun r state' =>
      exists m,
      r = tt /\
      m |= F * pn |-> File handle (mk_file data) /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Definition write_bypass_relation (handle : nat) (f : file) (m m' : mem pathname tree_node) : Prop :=
  (forall F pn f0, m |= F * pn |-> File handle f0 -> m' |= F * pn |-> File handle f) /\
  ((~ exists F pn f0, m |= F * pn |-> File handle f0) -> m' = m).

Definition write_bypass_spec pn data : Specification _ _ unit State :=
  fun '(F, filenum, f0) state => {|
    pre :=
      set_latest state |= F * pn |-> File filenum f0;
    post := fun r state' =>
      r = tt /\
      set_transform state state' (write_bypass_relation filenum (mk_file data));
    recovered := fun _ _ => False
  |}.

Definition find_available_name_spec tid dirpn : Specification _ _ unit State :=
  fun '(F, dirnum) state => {|
    pre :=
      set_latest state |= F * dirpn |-> Dir dirnum;
    post := fun r state' =>
      exists suffix, r = (tid ++ "."%string ++ suffix)%string /\
      state' = state /\
      set_latest state |= pred_eexcept F (dirpn ++ [r]) * (dirpn ++ [r]) |-> Missing * dirpn |-> Dir dirnum;
    recovered := fun _ _ => False
  |}.

Definition debug_spec : Specification _ _ unit State :=
  fun (_: unit) state => {|
    pre := True;
    post := fun r state' => state = state' /\ r = tt;
    recovered := fun _ _ => False
  |}.

Module Type FSAPI.

  Axiom init : proc InitResult.
  Axiom create : pathname -> string -> proc nat.
  Axiom mkdir : pathname -> string -> proc nat.
  Axiom delete : pathname -> proc unit.
  Axiom rmdir : pathname -> proc unit.
  Axiom rename_file : pathname -> pathname -> string -> proc unit.
  Axiom read : pathname -> proc string.
  Axiom write_logged : pathname -> string -> proc unit.
  Axiom write_bypass : pathname -> string -> proc unit.
  Axiom stat : pathname -> string -> proc stat_result.
  Axiom readdir : pathname -> proc (list string).
  Axiom recover : proc unit.
  Axiom find_available_name : pathname -> proc string.
  Axiom debug: string -> proc unit.
  
  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom create_ok : forall tid dir name, proc_spec (create_spec tid dir name) (create dir name) recover abstr.
  Axiom mkdir_ok : forall tid dir name, proc_spec (mkdir_spec tid dir name) (mkdir dir name) recover abstr.
  Axiom delete_ok : forall tid pn, proc_spec (delete_spec tid pn) (delete pn) recover abstr.
  Axiom rmdir_ok : forall tid pn, proc_spec (rmdir_spec tid pn) (rmdir pn) recover abstr.
  Axiom rename_file_ok : forall pn newdir newname, proc_spec (rename_file_spec pn newdir newname) (rename_file pn newdir newname) recover abstr.
  Axiom read_ok : forall pn, proc_spec (read_spec pn) (read pn) recover abstr.
  Axiom write_logged_ok : forall pn f, proc_spec (write_logged_spec pn f) (write_logged pn f) recover abstr.
  Axiom write_bypass_ok : forall pn f, proc_spec (write_bypass_spec pn f) (write_bypass pn f) recover abstr.
  Axiom stat_ok : forall pn n, proc_spec (stat_spec pn n) (stat pn n) recover abstr.
  Axiom readdir_ok : forall pn, proc_spec (readdir_spec pn) (readdir pn) recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_crash.
  Axiom find_available_name_ok :
    forall tid dirpn,
    proc_spec (find_available_name_spec tid dirpn) (find_available_name dirpn) recover abstr.
  Axiom debug_ok :  forall s, proc_spec (debug_spec) (debug s) recover abstr.


  Hint Resolve init_ok.
  Hint Resolve create_ok.
  Hint Resolve mkdir_ok.
  Hint Resolve delete_ok.
  Hint Resolve rmdir_ok.
  Hint Resolve rename_file_ok.
  Hint Resolve read_ok.
  Hint Resolve write_logged_ok.
  Hint Resolve write_bypass_ok.
  Hint Resolve stat_ok.
  Hint Resolve readdir_ok.
  Hint Resolve recover_noop.
  Hint Resolve find_available_name_ok.
  Hint Resolve debug_ok.

End FSAPI.
