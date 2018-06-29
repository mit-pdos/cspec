Require Import POCS.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.

Import ListNotations.
Require Import String.
Require Import FSAPI.

Definition message := string.

Inductive mailOpT : Type -> Type :=
| Deliver (user : string) (m : message) : mailOpT (option unit)
| Read (user : string) : mailOpT (option (list message)).

Definition mailState := forall (user : string), FSet.t message.

Definition upd (s : mailState) (u : string) v :=
  fun u' =>
    if string_dec u' u then v else s u'.


Module MailServerAPI <: Layer.

  Definition Op := mailOpT.
  Definition State := mailState.

  Inductive xstep : forall T, Op T -> nat -> State -> T -> State -> Prop :=
  | StepDeliver : forall user msg msgs state tid,
    state user = msgs ->
    xstep (Deliver user msg) tid
      state
      (Some tt)
      (upd state user (FSet.add msg msgs))
  | StepRead : forall user msgs state tid,
    state user = msgs ->
    xstep (Read user) tid
      state
      (Some (FSet.elements msgs))
      state
  | StepFail : forall T (op : Op (option T)) state tid,
    xstep op tid
      state
      None
      state.

  Definition step := xstep.

  Definition initP (_ : State) := True.

End MailServerAPI.
