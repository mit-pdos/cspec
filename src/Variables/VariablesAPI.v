Require Import POCS.


Inductive var :=
| VarCount
| VarSum.

Record State := mkState {
  StateCount : nat;
  StateSum : nat;
}.

Definition read_spec v : Specification _ _ unit _ :=
  fun '(count, sum) state => {|
    pre := StateCount state = count /\ StateSum state = sum;
    post := fun r state' =>
      state' = state /\
      match v with
      | VarCount => r = count
      | VarSum => r = sum
      end;
    recover := fun _ _ => False
  |}.

Definition write_spec v val : Specification _ _ unit _ :=
  fun '(count, sum) state => {|
    pre := StateCount state = count /\ StateSum state = sum;
    post := fun r state' =>
      r = tt /\
      match v with
      | VarCount => state' = mkState val sum
      | VarSum => state' = mkState count val
      end;
    recover := fun _ _ => False
  |}.


Module Type VarsAPI.

  Parameter init : prog InitResult.
  Parameter read : var -> prog nat.
  Parameter write : var -> nat -> prog unit.
  Parameter recover : prog unit.

  Axiom abstr : Abstraction State.

  Axiom read_ok : forall v, prog_spec (read_spec v) (read v) recover abstr.
  Axiom write_ok : forall v val, prog_spec (write_spec v val) (write v val) recover abstr.
  Axiom recover_noop : rec_noop recover abstr (@no_crash _).

  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve recover_noop.

End VarsAPI.
