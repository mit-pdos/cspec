Require Import Prog.
Require Import Automation.

Require Import Disk.SimpleDisk.
Require Import Refinement.Interface.

Module BadSectorDisk.

  Inductive Op : Type -> Type :=
  | Read (a:addr) : Op block
  | Write (a:addr) (b:block) : Op unit
  | GetBadSector : Op addr
  | DiskSize : Op nat.

  Record State :=
    mkState {
      stateDisk : disk;
      stateBadSector : addr;
    }.

  (* help out type inference *)
  Implicit Type (state:State).

  Inductive op_step : forall `(op: Op T), Semantics State T :=
  | step_read : forall a r (d : disk) bs,
      d a = Some r \/ d a = None \/ a = bs ->
      op_step (Read a) (mkState d bs) r (mkState d bs)
  | step_write : forall a b (d : disk) bs,
      op_step (Write a b) (mkState d bs) tt (mkState (diskUpd d a b) bs)
  | step_get_bs : forall d bs,
      bs < size d ->
      op_step GetBadSector (mkState d bs) bs (mkState d bs)
  | step_size : forall d bs,
      op_step DiskSize (mkState d bs) (size d) (mkState d bs).

  Definition crash state state' := state = state'.
  Definition bg_step state state' := state = state'.
  Definition inited state := True.

  Definition API : InterfaceAPI Op State :=
    {|
      op_sem := pre_step bg_step (@op_step);
      crash_effect := crash;
      init_sem := inited;
    |}.

  Ltac inv_step :=
    match goal with
    | [ H: op_step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      repeat sigT_eq;
      safe_intuition
    end.

  Ltac inv_bg :=
    match goal with
    | [ H: bg_step _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

End BadSectorDisk.
