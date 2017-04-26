Require Import Refinement.IO.
Require Import TwoDiskAPI TwoDiskImpl.
Require Import SeqDiskAPI.
Require Import Implements.
Require Import Automation.

(* D is an implementation of the single, sequential disk in DSpec. *)
Module D.
  Definition Read a :=
    v0 <- TD.Read d0 a;
      Ret v0.
  Definition Write a b :=
    _ <- TD.Write d0 a b;
      _ <- TD.Write d1 a b;
      Ret tt.

  Definition abstraction : TDSpec.State -> DSpec.State :=
    fun ds => DSpec.Disk (TDSpec.disk0 ds).

  Theorem Read_ok : forall a,
      implements
        (DSpec.Read a)
        (io_semantics (Read a))
        (fun w => abstraction (TD.abstraction w)).
  Proof.
    intros.
    unfold implements; simpl; intros.
    unfold Read in H.
    step.
    step.
    eapply TD.Read_ok in H; simpl in H; safe_intuition.
    destruct matches; intuition subst; try congruence.
  Qed.

  Theorem Write_ok : forall a b,
      implements
        (DSpec.Write a b)
        (io_semantics (Write a b))
        (fun w => abstraction (TD.abstraction w)).
  Proof.
    intros.
    unfold implements; simpl; intros.
    unfold Write in H.
    repeat step.
    repeat match goal with
           | [ H: io_step (TD.Write _ _ _) _ _ _ |- _ ] =>
             eapply TD.Write_ok in H; simpl in H; safe_intuition
           end.
    destruct matches; intuition subst.
    (* actually need to know invariant that domains are equal; implements
     relation should incorporate an invariant over the impl states *)
  Abort.

End D.
