Require Import POCS.


Definition State := list nat.

Definition inited (s : State) : Prop :=
  s = nil.

Definition add_spec v : Specification unit unit unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\ state' = v :: state;
    recover := fun _ _ => False
  |}.

Definition mean_spec : Specification unit (option nat) unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\
      (state = nil /\ r = None \/
       state <> nil /\ r = Some (fold_right plus 0 state / length state));
    recover := fun _ _ => False
  |}.


Module Type StatDbAPI.

  Parameter init : prog InitResult.
  Parameter add : nat -> prog unit.
  Parameter mean : prog (option nat).
  Parameter recover : prog unit.

  Parameter abstr : Abstraction State.

  Axiom init_ok : init_invariant init recover abstr inited.
  Axiom add_ok : forall v, prog_spec (add_spec v) (add v) recover abstr.
  Axiom mean_ok : prog_spec mean_spec mean recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_crash.

  Hint Resolve init_ok.
  Hint Resolve add_ok.
  Hint Resolve mean_ok.
  Hint Resolve recover_noop.

End StatDbAPI.
