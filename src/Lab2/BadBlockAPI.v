Require Import POCS.

Record State :=
  mkState {
    stateDisk : disk;
    stateBadBlock : addr;
  }.

Definition read_spec a : Specification _ block unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\
      a <> stateBadBlock state -> diskGet (stateDisk state) a ?|= eq r;
    recovered := fun _ state' => state' = state
  |}.

Definition write_spec a v : Specification _ _ unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\ state' = mkState (diskUpd (stateDisk state) a v) (stateBadBlock state);
    recovered := fun _ state' =>
      state' = state \/
      state' = mkState (diskUpd (stateDisk state) a v) (stateBadBlock state)
  |}.

Definition getBadBlock_spec : Specification _ addr unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\ r = stateBadBlock state;
    recovered := fun _ state' => state' = state
  |}.

Definition size_spec : Specification _ nat unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\ r = diskSize (stateDisk state);
    recovered := fun _ state' => state' = state
  |}.


Module Type BadBlockAPI.

  Axiom init : proc InitResult.
  Axiom read : addr -> proc block.
  Axiom write : addr -> block -> proc unit.
  Axiom getBadBlock : proc addr.
  Axiom size : proc nat.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
  Axiom write_ok : forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
  Axiom getBadBlock_ok : proc_spec getBadBlock_spec getBadBlock recover abstr.
  Axiom size_ok : proc_spec size_spec size recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_wipe.

  Hint Resolve init_ok.
  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve getBadBlock_ok.
  Hint Resolve size_ok.
  Hint Resolve recover_noop.

End BadBlockAPI.
