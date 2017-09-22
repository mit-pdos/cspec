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
  FileData : list nat;
}.

Definition empty_file := 
  mk_file nil.

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

Definition inited (s : State) : Prop :=
  set_older s = nil /\
  set_latest s |= nil |-> Dir 0 * empty_dir.

Definition create_spec dir name : Specification _ _ unit State :=
  fun '(F, dirnum) state => {|
    pre :=
      set_latest state |= F * dir |-> Dir dirnum * (dir ++ [name]) |-> Missing;
    post := fun r state' =>
      exists handle m,
      r = handle /\
      m |= F * dir |-> Dir dirnum * (dir ++ [name]) |-> File handle empty_file /\
      (forall mold,
       set_in mold state ->
       ~ exists F' pn f', mold |= F' * pn |-> File handle f') /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Definition mkdir_spec dir name : Specification _ _ unit State :=
  fun '(F, dirnum) state => {|
    pre :=
      set_latest state |= F * dir |-> Dir dirnum * (dir ++ [name]) |-> Missing;
    post := fun r state' =>
      exists newdirnum m,
      r = newdirnum /\
      m |= F * dir |-> Dir dirnum * (dir ++ [name]) |-> Dir newdirnum *
           subtree_pred (dir ++ [name]) empty_dir /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Definition delete_spec pn : Specification _ _ unit State :=
  fun '(F, handle, f) state => {|
    pre :=
      set_latest state |= F * pn |-> File handle f;
    post := fun r state' =>
      exists m,
      r = tt /\
      m |= F * pn |-> Missing /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Definition rmdir_spec pn : Specification _ _ unit State :=
  fun '(F, dirnum) state => {|
    pre :=
      set_latest state |= F * pn |-> Dir dirnum * subtree_pred pn empty_dir;
    post := fun r state' =>
      exists m,
      r = tt /\
      m |= F * pn |-> Missing /\
      state' = set_add state m;
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
      r = f /\
      state' = state;
    recovered := fun _ _ => False
  |}.

Definition write_logged_spec pn f : Specification _ _ unit State :=
  fun '(F, handle, f0) state => {|
    pre :=
      set_latest state |= F * pn |-> File handle f0;
    post := fun r state' =>
      exists m,
      r = tt /\
      m |= F * pn |-> File handle f /\
      state' = set_add state m;
    recovered := fun _ _ => False
  |}.

Definition write_bypass_relation (handle : nat) (f : file) (m m' : mem pathname tree_node) : Prop :=
  (forall F pn f0, m |= F * pn |-> File handle f0 -> m' |= F * pn |-> File handle f) /\
  ((~ exists F pn f0, m |= F * pn |-> File handle f0) -> m' = m).

Definition write_bypass_spec pn f : Specification _ _ unit State :=
  fun '(F, filenum, f0) state => {|
    pre :=
      set_latest state |= F * pn |-> File filenum f0;
    post := fun r state' =>
      r = tt /\
      set_transform state state' (write_bypass_relation filenum f);
    recovered := fun _ _ => False
  |}.


Module Type FSAPI.

  Axiom init : proc InitResult.
  Axiom create : pathname -> string -> proc nat.
  Axiom mkdir : pathname -> string -> proc nat.
  Axiom delete : pathname -> proc unit.
  Axiom rmdir : pathname -> proc unit.
  Axiom rename_file : pathname -> pathname -> string -> proc unit.
  Axiom read : pathname -> proc file.
  Axiom write_logged : pathname -> file -> proc unit.
  Axiom write_bypass : pathname -> file -> proc unit.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom create_ok : forall dir name, proc_spec (create_spec dir name) (create dir name) recover abstr.
  Axiom mkdir_ok : forall dir name, proc_spec (mkdir_spec dir name) (mkdir dir name) recover abstr.
  Axiom delete_ok : forall pn, proc_spec (delete_spec pn) (delete pn) recover abstr.
  Axiom rmdir_ok : forall pn, proc_spec (rmdir_spec pn) (rmdir pn) recover abstr.
  Axiom rename_file_ok : forall pn newdir newname, proc_spec (rename_file_spec pn newdir newname) (rename_file pn newdir newname) recover abstr.
  Axiom read_ok : forall pn, proc_spec (read_spec pn) (read pn) recover abstr.
  Axiom write_logged_ok : forall pn f, proc_spec (write_logged_spec pn f) (write_logged pn f) recover abstr.
  Axiom write_bypass_ok : forall pn f, proc_spec (write_bypass_spec pn f) (write_bypass pn f) recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_crash.

  Hint Resolve init_ok.
  Hint Resolve create_ok.
  Hint Resolve mkdir_ok.
  Hint Resolve delete_ok.
  Hint Resolve rmdir_ok.
  Hint Resolve rename_file_ok.
  Hint Resolve read_ok.
  Hint Resolve write_logged_ok.
  Hint Resolve write_bypass_ok.
  Hint Resolve recover_noop.

End FSAPI.
