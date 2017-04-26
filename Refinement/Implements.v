(** Proving implementations correct via an abstraction relation between two
semantics. *)
Require Import Refinement.IO.

(** A [Semantics] is a general way to describe a transition; a given operation
   will have a particular semantics, whereas a layer will have several semantics
   that all share the same state and are thus comparable.

   One can think of a [Semantics T] as a fragment of step, and one that produces
   a T-typed result. *)
Record Semantics T :=
  NewSem { State : Type;
           Step : State -> T -> State -> Prop; }.

Definition io_semantics T (p:IO T) : Semantics T :=
  {| State := world;
     Step := io_step p; |}.

Section Implements.
  Variable T:Type.
  Variable Impl:Semantics T.
  Variable Spec:Semantics T.
  Variable abstraction: State Impl -> State Spec.

  Implicit Type t : State Impl.
  Implicit Type s : State Spec.

  (* A proof of [implements] shows that [Impl] implements [Spec] via an
  abstraction function [abstraction]. *)
  Definition implements :=
    forall t v t', Step Impl t v t' ->
              Step Spec (abstraction t) v (abstraction t').

End Implements.
