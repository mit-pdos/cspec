Require Import POCS.

Module Vars.

  Inductive var :=
  | VarCount
  | VarSum.

  Axiom init : prog InitResult.
  Axiom read : var -> prog nat.
  Axiom write : var -> nat -> prog unit.
  Axiom var_recover : prog unit.


  (** The state the program manipulates as it executes. *)
  Record State := mkState {
    StateCount : nat;
    StateSum : nat;
  }.

  Axiom abstr : Abstraction State.


  Axiom read_ok : forall v,
    prog_spec
      (fun '(count, sum) state => {|
        pre := StateCount state = count /\ StateSum state = sum;
        post := fun r state' =>
          state' = state /\
          match v with
          | VarCount => r = count
          | VarSum => r = sum
          end;
        recover := fun _ _ => False
      |})
      (read v) var_recover abstr.
  Hint Resolve read_ok.

  Axiom write_ok : forall v val,
    prog_spec
      (fun '(count, sum) state => {|
        pre := StateCount state = count /\ StateSum state = sum;
        post := fun r state' =>
          r = tt /\
          match v with
          | VarCount => state' = mkState val sum
          | VarSum => state' = mkState count val
          end;
        recover := fun _ _ => False
      |})
      (write v val) var_recover abstr.
  Hint Resolve write_ok.


  Definition wipe (state state' : State) := False.

  Axiom recover_noop : rec_noop var_recover abstr wipe.
  Hint Resolve recover_noop.

End Vars.

Extraction Language Haskell.

Extract Constant Vars.read => "Variables.read".
Extract Constant Vars.write => "Variables.write".
Extract Constant Vars.abstr => "Hoare.Build_LayerAbstraction".
