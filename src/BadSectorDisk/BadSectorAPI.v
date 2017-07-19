Require Import POCS.

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
      a <> bs -> d a = Some r ->
      op_step (Read a) (mkState d bs) r (mkState d bs)
  | step_read_oob : forall a r (d : disk) bs,
      a <> bs -> d a = None ->
      op_step (Read a) (mkState d bs) r (mkState d bs)
  | step_read_bad : forall a r (d : disk) bs,
      a = bs ->
      op_step (Read a) (mkState d bs) r (mkState d bs)
  | step_write : forall a b (d : disk) bs,
      op_step (Write a b) (mkState d bs) tt (mkState (diskUpd d a b) bs)
  | step_get_bs : forall d bs,
      op_step GetBadSector (mkState d bs) bs (mkState d bs)
  | step_size : forall d bs,
      op_step DiskSize (mkState d bs) (size d) (mkState d bs).

  Definition crash_relation state state' := False.
  Definition bg_step state state' := state = state'.
  Definition inited state := True.

  Definition API : InterfaceAPI Op State :=
    {|
      op_sem := pre_step bg_step (@op_step);
      crash_effect := crash_relation;
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
