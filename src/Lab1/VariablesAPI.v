Require Import POCS.

(** * Specification of Variables.

  There are only two variables: [VarCount] and [VarSum], which can be
  initialized, read, and written.  The specification for [read] and [write] are
  given by [read_spec] and [write_spec], respectively. 

 *)

(** There are two variables, named as follows: *)
Inductive var :=
| VarCount
| VarSum.

(** The values of these variables are the spec state: *)
Record State := mkState {
  StateCount : nat;
  StateSum : nat;
}.

(** An implementation of [read] has the precondition that the value of
  [StateCount state] = count and [StateSum state] = sum. The postcondition
  states the value returned by [read] is either count or sum, depending on which
  variable is read. *)

Definition read_spec v : Specification _ _ unit _ :=
  fun '(count, sum) state => {|
    pre := StateCount state = count /\ StateSum state = sum;
    post := fun r state' =>
      state' = state /\
      match v with
      | VarCount => r = count
      | VarSum => r = sum
      end;
    recovered := fun _ _ => False
  |}.

(** An implementation of [write] has the same precondition as [read].  The
  postcondition states that new spec is a new state in which either [StateCount]
  or [StateSum] is updated, depending on which variable [write] writes. The
  return value is tt. *)

Definition write_spec v val : Specification _ _ unit _ :=
  fun '(count, sum) state => {|
    pre := StateCount state = count /\ StateSum state = sum;
    post := fun r state' =>
      r = tt /\
      match v with
      | VarCount => state' = mkState val sum
      | VarSum => state' = mkState count val
      end;
    recovered := fun _ _ => False
  |}.


(** * Variables module

   An implementation (the code) of Variables must implement the following
   Variables module (the spec).

  *)

Module Type VarsAPI.

  Axiom init : proc InitResult.
  Axiom read : var -> proc nat.
  Axiom write : var -> nat -> proc unit.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall v, proc_spec (read_spec v) (read v) recover abstr.
  Axiom write_ok : forall v val, proc_spec (write_spec v val) (write v val) recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_crash.

  Hint Resolve init_ok.
  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve recover_noop.

End VarsAPI.
