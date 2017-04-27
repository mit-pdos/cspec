(** Proving implementations correct via an abstraction relation between two
semantics. *)
Require Export Refinement.IO.

(** A [Semantics] is a general way to describe a transition; a given operation
   will have a particular semantics, whereas a layer will have several semantics
   that all share the same state and are thus comparable.

   One can think of a [Semantics T] as a fragment of step, and one that produces
   a T-typed result. *)
Record Semantics T :=
  (* we name the constructor for [Semantics] StepRel since it takes State
  implicitly and thus converts a relation to a Semantics. *)
  StepRel { State : Type;
            (* when [Step state r state'] holds, then this operation can step from [state]
            to [state'] and return [r]. *)
            Step : State -> T -> State -> Prop; }.

Section Implements.
  Variable T:Type.
  Variable Spec:Semantics T.
  Variable Impl:IO T.
  Variable abstraction: world -> State Spec.
  Variable invariant : world -> Prop.

  (* A proof of [implements] shows that [Impl] implements [Spec] via an
  abstraction function [abstraction], preserving [invariant].

   The order of the arguments is chosen to go from more interesting to less
   interesting:
   - the spec determines what we're trying to prove
   - the implementation is some concrete program written based on existing
     functions and primitives
   - the abstraction relation is both a proof tool and defines how physical
     states line up
   - the invariant is mostly a proof tool, although it can't be too restrictive
     since the system must be started from a state satisfying this predicate
   *)
  Definition implements :=
    forall t v t', io_step Impl t v t' ->
              invariant t ->
              Step Spec (abstraction t) v (abstraction t') /\
              invariant t'.

End Implements.

(* automation to hide abstraction of lower levels *)

Local Ltac hide_fn_call fn arg :=
  generalize dependent (fn arg); clear arg; intros arg ??.

(** hide_fn abstraction will abstract [abstraction t] to an opaque term t; use
 to replace a lower-level abstractions that need not be unfolded. *)
Tactic Notation "hide_fn" constr(fn) :=
  repeat match goal with
         | |- context[fn ?arg] => hide_fn_call fn arg
         | H: context[fn ?arg] |- _ => hide_fn_call fn arg
         end.
