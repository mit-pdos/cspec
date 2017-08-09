Require Import POCS.


Definition State := list nat.

Definition inited (s : State) : Prop :=
  s = nil.

Definition add_spec v : Specification unit unit unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\ state' = v :: state;
    recovered := fun _ _ => False
  |}.

Definition mean_spec : Specification unit (option nat) unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\
      (state = nil /\ r = None \/
       state <> nil /\ r = Some (fold_right plus 0 state / length state));
    recovered := fun _ _ => False
  |}.


Module Type StatDbAPI.

  Axiom init : proc InitResult.
  Axiom add : nat -> proc unit.
  Axiom mean : proc (option nat).
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
  Axiom mean_ok : proc_spec mean_spec mean recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_crash.

  Hint Resolve init_ok.
  Hint Resolve add_ok.
  Hint Resolve mean_ok.
  Hint Resolve recover_noop.

End StatDbAPI.
