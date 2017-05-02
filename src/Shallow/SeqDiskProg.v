Require Import Prog.
Require Import Disk.

(* Defines programs over a single disk. *)

Module D.

  Inductive Op : Type -> Type :=
  | Read (a:addr) : Op block
  | Write (a:addr) (b:block) : Op unit.

  Definition prog := Prog.prog Op.

  Definition State := disk.

  Inductive step : Semantics Op State :=
  | step_read : forall a b (state: State),
      (forall b0, state a = Some b0 -> b = b0) ->
      step (Read a) state b state
  | step_write : forall a b state,
      step (Write a b) state tt (diskUpd state a b).

  Definition exec := Prog.exec step.
  Definition exec_recover := Prog.exec_recover step.

End D.
