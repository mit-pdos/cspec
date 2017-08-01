Require Import POCS.


Definition State := disk.

Definition read_spec a : Specification _ block unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\
      state a ?|= eq r;
    recover := fun _ state' =>
      state' = state
  |}.

Definition write_spec a v : Specification _ _ unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\ state' = diskUpd state a v;
    recover := fun _ state' =>
      state' = state \/ state' = diskUpd state a v
  |}.

Definition diskSize_spec : Specification _ nat unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\ r = size state;
    recover := fun _ state' =>
      state' = state
  |}.


Module Type OneDiskAPI.

  Parameter init : prog InitResult.
  Parameter read : addr -> prog block.
  Parameter write : addr -> block -> prog unit.
  Parameter diskSize : prog nat.
  Parameter recover : prog unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall a, prog_spec (read_spec a) (read a) recover abstr.
  Axiom write_ok : forall a v, prog_spec (write_spec a v) (write a v) recover abstr.
  Axiom diskSize_ok : prog_spec diskSize_spec diskSize recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_wipe.

  Hint Resolve init_ok.
  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve diskSize_ok.
  Hint Resolve recover_noop.

End OneDiskAPI.