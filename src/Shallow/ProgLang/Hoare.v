(** Crash Hoare Logic specifications *)

(* TODO: document how specifications are structured *)

Require Import Automation.
Require Import Prog.
Require Import ProgTheorems.

Set Implicit Arguments.

(** * refinement composition *)

(* A LRefinement (for "layer refinement") goes between State1 (implementation)
and State2 (spec) *)
Record LRefinement State1 State2 :=
  { invariant : State1 -> Prop;
    abstraction : State1 -> State2; }.

(* TODO: come up with a good, short name for terms of type Refinement (currently
using [rf], which I'm not too happy with) *)
Definition Refinement State := LRefinement world State.

Definition refinement_compose
           `(rf1: Refinement State1)
           `(rf2: LRefinement State1 State2) :=
  {| invariant := fun w => invariant rf1 w /\
                        invariant rf2 (abstraction rf1 w);
     abstraction := fun w => abstraction rf2 (abstraction rf1 w); |}.
