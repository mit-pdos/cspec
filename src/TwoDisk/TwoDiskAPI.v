Require Import POCS.
Require Export TwoDisk.TwoDiskBaseAPI.


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
        d a ?|= eq v
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
       get_disk i state' ?|= eq (diskUpd d a b) /\ a < size d) /\
      get_disk (other i) state' ?|= F;
  |}.

Definition diskSize_spec (i : diskId) : Specification _ _ unit _ :=
  fun '(d, F) state => {|
    pre :=
      get_disk i         state ?|= eq d /\
      get_disk (other i) state ?|= F;
    post := fun r state' =>
      match r with
      | Working n =>
        get_disk i         state' ?|= eq d /\
        get_disk (other i) state' ?|= F /\
        n = size d
      | Failed =>
        get_disk i         state' ?|= missing /\
        get_disk (other i) state' ?|= F
      end;
    recover := fun _ state' =>
      get_disk i         state' ?|= eq d /\
      get_disk (other i) state' ?|= F;
  |}.


Module Type TwoDiskAPI.

  Parameter init : prog InitResult.
  Parameter read : diskId -> addr -> prog (DiskResult block).
  Parameter write : diskId -> addr -> block -> prog (DiskResult unit).
  Parameter diskSize : diskId -> prog (DiskResult nat).
  Parameter recover : prog unit.

  Axiom abstr : Abstraction State.

  Axiom read_ok : forall i a, prog_spec (read_spec i a) (read i a) recover abstr.
  Axiom write_ok : forall i a v, prog_spec (write_spec i a v) (write i a v) recover abstr.
  Axiom diskSize_ok : forall i, prog_spec (diskSize_spec i) (diskSize i) recover abstr.
  Axiom recover_noop : rec_noop recover abstr (@no_wipe _).

  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve diskSize_ok.
  Hint Resolve recover_noop.

End TwoDiskAPI.
