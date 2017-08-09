Require Import POCS.
Require Export TwoDiskBaseAPI.


Definition other (i : diskId) :=
  match i with
  | d0 => d1
  | d1 => d0
  end.

Definition read_spec (i : diskId) (a : addr) : Specification _ _ unit _ :=
  fun '(d, F) state => {|
    pre :=
      get_disk i         state ?|= eq d /\
      get_disk (other i) state ?|= F;
    post := fun r state' =>
      match r with
      | Working v =>
        get_disk i         state' ?|= eq d /\
        get_disk (other i) state' ?|= F /\
        diskGet d a ?|= eq v
      | Failed =>
        get_disk i         state' ?|= missing /\
        get_disk (other i) state' ?|= F
      end;
    recover := fun _ state' =>
      get_disk i         state' ?|= eq d /\
      get_disk (other i) state' ?|= F;
  |}.

Definition write_spec (i : diskId) (a : addr) (b : block) : Specification _ (DiskResult unit) unit _ :=
  fun '(d, F) state => {|
    pre :=
      get_disk i         state ?|= eq d /\
      get_disk (other i) state ?|= F;
    post := fun r state' =>
      match r with
      | Working _ =>
        get_disk i         state' ?|= eq (diskUpd d a b) /\
        get_disk (other i) state' ?|= F
      | Failed =>
        get_disk i         state' ?|= missing /\
        get_disk (other i) state' ?|= F
      end;
    recover := fun _ state' =>
      (get_disk i state' ?|= eq d \/
       get_disk i state' ?|= eq (diskUpd d a b) /\ a < diskSize d) /\
      get_disk (other i) state' ?|= F;
  |}.

Definition size_spec (i : diskId) : Specification _ _ unit _ :=
  fun '(d, F) state => {|
    pre :=
      get_disk i         state ?|= eq d /\
      get_disk (other i) state ?|= F;
    post := fun r state' =>
      match r with
      | Working n =>
        get_disk i         state' ?|= eq d /\
        get_disk (other i) state' ?|= F /\
        n = diskSize d
      | Failed =>
        get_disk i         state' ?|= missing /\
        get_disk (other i) state' ?|= F
      end;
    recover := fun _ state' =>
      get_disk i         state' ?|= eq d /\
      get_disk (other i) state' ?|= F;
  |}.


Module Type TwoDiskAPI.

  Axiom init : proc InitResult.
  Axiom read : diskId -> addr -> proc (DiskResult block).
  Axiom write : diskId -> addr -> block -> proc (DiskResult unit).
  Axiom size : diskId -> proc (DiskResult nat).
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall i a, proc_spec (read_spec i a) (read i a) recover abstr.
  Axiom write_ok : forall i a v, proc_spec (write_spec i a v) (write i a v) recover abstr.
  Axiom size_ok : forall i, proc_spec (size_spec i) (size i) recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_wipe.

  Hint Resolve init_ok.
  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve size_ok.
  Hint Resolve recover_noop.

End TwoDiskAPI.
