Require Import POCS.

(** * Specification of Variables.

  This layer provides support for manipulating mutable variables, for the
  purposes of implementing the StatDB API. We use axioms to specify this layer
  in [POCS.Lab1.VariablesImpl] and provide the executable implementations in
  Haskell.

  There are only two variables: [VarCount] and [VarSum], which can be
  initialized, read, and written. The specifications for [read] and [write] are
  given by [read_spec] and [write_spec], respectively.

 *)

(** There are two variables, which are referred to using this type. *)
Inductive var :=
| VarCount
| VarSum.

(** The values of these variables are the spec state: *)
Record State := mkState {
  StateCount : nat;
  StateSum : nat;
}.

(** The precondition for read is a function that takes two arguments: a pair
  [(count,sum)] and a spec state [state] and asserts a proposition about them. The
  way to read this is that the precondition states that there exists a pair
  [(count,sum)] and a [state] such that the value of [StateCount state] is [count] and
  [StateSum state] is [sum].

  The postcondition states the value returned by [read] is either [count] or
  [sum], depending on which variable is read. *)

Definition read_spec v : Specification _ _ _ :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\
      match v with
      | VarCount => r = StateCount state
      | VarSum => r = StateSum state
      end;
  |}.

(** An implementation of [write] has the same precondition as [read].  The
  postcondition states that the new spec state has either [StateCount]
  or [StateSum] is updated, depending on which variable [write] writes. The
  return value is tt. *)

Definition write_spec v val : Specification _ _ _ :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\
      match v with
      | VarCount => state' = mkState val (StateSum state)
      | VarSum => state' = mkState (StateCount state) val
      end;
  |}.


(** * Variables module

   An implementation of Variables must implement the following module type and
   must prove that that its code implements the spec correctly using refinement.
   Our implementation of the module, [VariablesImpl], is in Haskell and assumes
   that the Haskell implementation meets the required specification.

  *)

Module Type VarsAPI.

  Axiom init : proc InitResult.
  Axiom read : var -> proc nat.
  Axiom write : var -> nat -> proc unit.

  Axiom abstr : Abstraction State.

  (* Note that [inited_any] allows any initial state, meaning StatDB is required
     to initialize its variables appropriately. *)
  Axiom init_ok : init_abstraction init abstr inited_any.
  Axiom read_ok : forall v, proc_spec (read_spec v) (read v) abstr.
  Axiom write_ok : forall v val, proc_spec (write_spec v val) (write v val) abstr.

  Hint Resolve init_ok.
  Hint Resolve read_ok.
  Hint Resolve write_ok.

End VarsAPI.
