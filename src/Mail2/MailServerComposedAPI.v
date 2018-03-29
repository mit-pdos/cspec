Require Import POCS.
Require Import String.
Require Import MailServerAPI.


Module MailServerComposedOp <: Ops.

  Import MailServerOp.
  Definition user := validIndexT UserIdx.indexValid.

  Inductive xopT : Type -> Type :=
  | Deliver : forall (u : user) (m : string), xopT bool
  | Pickup : forall (u : user), xopT (list ((nat*nat) * string))
  | CheckUser : forall (u : string), xopT (CheckResult UserIdx.indexValid)
  | Delete : forall (u : user) (id : nat*nat), xopT unit
  | Ext : forall `(op : extopT T), xopT T
  .

  Definition opT := xopT.

End MailServerComposedOp.


Module MailServerComposedState := MailServerHState.


Module MailServerComposedAPI <: Layer MailServerComposedOp MailServerComposedState.

  Import MailServerComposedOp.
  Import MailServerComposedState.

  Inductive xstep : forall T, opT T -> nat -> State -> T -> State -> list event -> Prop :=
  | StepDeliverOK : forall m s u fn tid,
    ~ FMap.In fn (hget s u) ->
    xstep (Deliver u m) tid
      s
      true
      (hadd u (FMap.add fn m (hget s u)) s)
      nil
  | StepDeliverErr : forall m s u tid,
    xstep (Deliver u m) tid
      s
      false
      s
      nil
  | StepPickup : forall s tid r u,
    FMap.is_permutation_kv r (hget s u) ->
    xstep (Pickup u) tid
      s
      r
      s
      nil
  | StepDelete : forall s tid id u,
    xstep (Delete u id) tid
      s
      tt
      (hadd u (FMap.remove id (hget s u)) s)
      nil

  | StepCheckUser : forall s tid u r,
    sameSlice r u ->
    xstep (CheckUser u) tid
      s
      r
      s
      nil

  | StepExt : forall s tid `(extop : _ T) r,
    xstep (Ext extop) tid
      s
      r
      s
      (Event (extop, r) :: nil)
  .

  Definition step := xstep.

End MailServerComposedAPI.
