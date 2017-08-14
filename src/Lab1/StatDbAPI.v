Require Import POCS.

(** * Specification for StatDB

    An implementation of StatDB will have to prove that its implementation meets
    the specification stated in this file.  The specification for StatDB
    contains three parts:

    - The state of the StatDB: a list of integers

    - An initial state: the list of integers is nil

    - Two operations: add and mean. The specification for each operation is
    stated in terms of a precondition and a postcondition.  (Each operation also
    has a recovered condition, but we will ignore crash conditions in this lab.)

*)



(** ** The state of StatDB
   
  We will often refer to the state that specification maintains as the spec state.
 *)

Definition State := list nat.

(** ** The initial value of the spec state:
 *)

Definition inited (s : State) : Prop :=
  s = nil.

(** ** The specification of the StatDB operations

  The specifications are of type [Specification], which is defined in
  [POCS.Refinement.Hoare]. A specificatoin is a record with 3 fields: [pre],
  [post], and [recovered] (which we will ignore in this lab).  For both
  operations the precondition is just [True] (i.e., the operations can be always
  invoked).  The postconditions describe the effects of the operations [add] and
  [mean]:

  - [add_spec]'s post condition states that [add v] adds [v] to the spec state
    of StatDB and that [add] returns [tt].

  - [mean_spec]'s post condition states that [mean] doesn't modify the spec
    state of StatDB, and that its return value is one of two values: (1) if
    state is [nil], then the return value is [None]; (2) if state is not [nil],
    then the return value is the average of the numbers in StatDB's state.

 *)

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


(** * StatDB module

   An implementation (the code) of StatDB must implement the StatDB module (the
   spec).  The module must provide implementation for [init], [add], [mean], and
   [recovery] (which will be a NOOP).  In addition, the module must provide
   proofs showing, for example, that its [add] implementation meets the
   [add_spec].  The proof approach POCS uses is based on backwards simulation
   and this approach requires the implementation to define [abstr], which
   abstracts the code state to the spec state (the list of integers that StatDB
   maintains).  [abstr] is of type [Refinement.Hoare.Abstraction].

*)


Module Type StatDbAPI.

  (** The implementation must provide the following methods: *)
  Axiom init : proc InitResult.
  Axiom add : nat -> proc unit.
  Axiom mean : proc (option nat).
  Axiom recover : proc unit.

  (** The abstraction relation between spec and code state *)
  Axiom abstr : Abstraction State.

  (** The proofs that the implementation methods meet their specs: *)
  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
  Axiom mean_ok : proc_spec mean_spec mean recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_crash.

  (** Hints to proof automation to apply the following proofs. The implementation
  doesn't have to be concerned with these hints. *)
  Hint Resolve init_ok.
  Hint Resolve add_ok.
  Hint Resolve mean_ok.
  Hint Resolve recover_noop.

End StatDbAPI.
