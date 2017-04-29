Require Import Prog.
Require Import Disk.

(* Defines programs over a single disk. *)

Module D.

  Inductive Op : Type -> Type :=
  | Read (a:addr) : Op block
  | Write (a:addr) (b:block) : Op unit.

  Definition prog := Prog.prog Op.

  Record State :=
    SDisk { sdisk: disk }.

  Inductive step : Semantics Op State :=
  | step_read : forall a b state,
      (forall b0, sdisk state a = Some b0 -> b = b0) ->
      step (Read a) state b state
  | step_write : forall a b state,
      let disk' := match sdisk state a with
                   | Some _ => upd (sdisk state) a b
                   | None => sdisk state
                   end in
      step (Write a b) state tt (SDisk disk').

  Definition exec := Prog.exec step.
  Definition exec_recover := Prog.exec_recover step.

End D.
