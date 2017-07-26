Require Import POCS.

Record State :=
  mkState {
    stateDisk : disk;
    stateBadSector : addr;
  }.

Definition read_spec a : Specification _ block unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\
      (stateDisk state) a ?|= eq r;
    recover := fun _ _ => False
  |}.

Definition write_spec a v : Specification _ _ unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\ state' = mkState (diskUpd (stateDisk state) a v) (stateBadSector state);
    recover := fun _ _ => False
  |}.

Definition getBadSector_spec : Specification _ addr unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\ r = stateBadSector state;
    recover := fun _ _ => False
  |}.

Definition diskSize_spec : Specification _ nat unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\ r = size (stateDisk state);
    recover := fun _ _ => False
  |}.

Definition wipe (state state' : State) := False.


Module Type BadSectorAPI.

  Parameter init : prog InitResult.
  Parameter read : addr -> prog block.
  Parameter write : addr -> block -> prog unit.
  Parameter getBadSector : prog addr.
  Parameter diskSize : prog nat.
  Parameter recover : prog unit.

  Axiom abstr : Abstraction State.

  Axiom read_ok : forall a, prog_spec (read_spec a) (read a) recover abstr.
  Axiom write_ok : forall a v, prog_spec (write_spec a v) (write a v) recover abstr.
  Axiom getBadSector_ok : prog_spec getBadSector_spec getBadSector recover abstr.
  Axiom diskSize_ok : prog_spec diskSize_spec diskSize recover abstr.
  Axiom recover_noop : rec_noop recover abstr wipe.

  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve getBadSector_ok.
  Hint Resolve diskSize_ok.
  Hint Resolve recover_noop.

End BadSectorAPI.
