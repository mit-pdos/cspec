Require Import POCS.
Require Import FSAPI.

Import ListNotations.
Require Import String.

Extraction Language Haskell.

Module FS <: FSAPI.

  Definition pathname := FSAPI.pathname.

  Axiom init : proc InitResult.
  Axiom create : pathname -> string -> proc nat.
  Axiom mkdir : pathname -> string -> proc nat.
  Axiom delete : pathname -> proc unit.
  Axiom rmdir : pathname -> proc unit.
  Axiom rename_file : pathname -> pathname -> string -> proc unit.
  Axiom read : pathname -> proc string.
  Axiom write_logged : pathname -> string -> proc unit.
  Axiom write_bypass : pathname -> string -> proc unit.
  Axiom stat : pathname -> string -> proc FSAPI.stat_result.
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
  Axiom find_available_name_ok :  forall tid dirpn,
    proc_spec (find_available_name_spec tid dirpn) (find_available_name dirpn) recover abstr.
  Axiom debug_ok :  forall s, proc_spec (debug_spec) (debug s) recover abstr.


End FS.

Extract Constant FS.init => "FS.Ops.init".
Extract Constant FS.create => "FS.Ops.create".
Extract Constant FS.mkdir => "FS.Ops.mkdir".
Extract Constant FS.write_logged => "FS.Ops.write_logged".
Extract Constant FS.debug => "FS.Ops.debug".

(* XXX should be split: it should call find_avaialbe_name, but we should check
 * in Gallina that the name returned is indeed available and proof the check
 * correct.  For now completely trusted. *)
Extract Constant FS.find_available_name => "FS.Ops.find_available_name".

