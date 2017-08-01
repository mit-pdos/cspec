Require Import POCS.
Require Import StatDbImpl.
Require Import VariablesImpl.


Module statdb := StatDB Vars.

Axiom get_new_item : prog nat.
Axiom report_mean : option nat -> prog unit.


CoFixpoint loop : prog unit :=
  m <- statdb.mean;
  _ <- report_mean m;
  x <- get_new_item;
  _ <- statdb.add x;
  loop.

Definition cli : prog unit :=
  init_ok <- statdb.init;
  match init_ok with
  | Initialized =>
    loop
  | InitFailed =>
    Ret tt
  end.

Extract Constant get_new_item => "CLI.getNewItem".
Extract Constant report_mean => "CLI.reportMean".