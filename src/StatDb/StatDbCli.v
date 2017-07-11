Require Import POCS.
Require Import StatDb.StatDbAPI.
Require Import StatDb.StatDbImpl.
Require Import Variables.ExtrVariables.

Axiom get_new_item : prog nat.
Axiom report_mean : option nat -> prog unit.

Definition statdb := StatDB.statdb Vars.vars.

CoFixpoint loop : prog unit :=
  m <- Prim statdb StatDB.Mean;
  _ <- report_mean m;
  x <- get_new_item;
  _ <- Prim statdb (StatDB.Add x);
  loop.

Definition cli : prog unit :=
  init_ok <- iInit statdb;
  match init_ok with
  | Initialized =>
    loop
  | InitFailed =>
    Ret tt
  end.

Extract Constant get_new_item => "CLI.getNewItem".
Extract Constant report_mean => "CLI.reportMean".
