Require Import POCS.


Definition State : Type := block*block.

Definition get_spec : Specification unit (block*block) unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' => r = state;
    recover := fun _ state' => state' = state
  |}.

Definition put_spec v : Specification unit unit unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' => r = tt /\ state' = v;
    recover := fun _ state' => state' = state \/ state' = v
  |}.


Module Type AtomicPairAPI.

  Parameter init : prog InitResult.
  Parameter get : prog (block*block).
  Parameter put : block*block -> prog unit.
  Parameter recover : prog unit.

  Parameter abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom get_ok : prog_spec get_spec get recover abstr.
  Axiom put_ok : forall v, prog_spec (put_spec v) (put v) recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_wipe.

  Hint Resolve init_ok.
  Hint Resolve get_ok.
  Hint Resolve put_ok.
  Hint Resolve recover_noop.

End AtomicPairAPI.