Require Import CSPEC.
Require Import String.
Require Import MailServerAPI.


Module MailServerComposedOp.

  Import MailServerOp.
  Definition user := validIndexT UserIdx.idx.

  Inductive xOp : Type -> Type :=
  | Deliver : forall (u : user) (m : string), xOp bool
  | Pickup : forall (u : user), xOp (list ((nat*nat) * string))
  | CheckUser : forall (u : string), xOp (CheckResult UserIdx.idx)
  | Delete : forall (u : user) (id : nat*nat), xOp unit
  | Ext : forall `(op : extopT T), xOp T
  .

  Definition Op := xOp.

End MailServerComposedOp.


Module MailServerComposedState.
  Definition State := MailServerHState.
End MailServerComposedState.


Module MailServerComposedAPI.

  Import MailServerComposedOp.
  Import MailServerComposedState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> list event -> Prop :=
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

  | StepCheckUser : forall s tid (u: UserIdx.idx) r,
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

  Definition initP : MailServerComposedState.State -> Prop := horizInitP MailServerState.initP.

End MailServerComposedAPI.
