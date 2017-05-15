Require Import Automation.
Require Import Implements.
Require Import
        Refinement.TwoDiskAPI
        Refinement.TwoDiskImpl.
Require Import Refinement.SeqDiskAPI.

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

  Definition invariant (ds:TDSpec.State) :=
    size (TDSpec.disk0 ds) = size (TDSpec.disk1 ds).

  Theorem Read_ok : forall a,
      implements
        (DSpec.Read a)
        (Read a)
        (fun w => abstraction (TD.abstraction w))
        (fun w => invariant (TD.abstraction w)).
  Proof.
    intros.
    unfold implements; simpl; intros.
    unfold Read in H.
    step.
    step.
    eapply TD.Read_ok in H; simpl in H; safe_intuition.
    destruct matches; intuition (subst; eauto); try congruence.
  Qed.

  Lemma invariant_stable_upd : forall d_0 d_1 a b,
      invariant (TDSpec.Disks d_0 d_1) ->
      invariant (TDSpec.Disks (diskUpd d_0 a b) (diskUpd d_1 a b)).
  Proof.
    unfold invariant; simpl; intros.
    autorewrite with upd; auto.
  Qed.

  Hint Resolve invariant_stable_upd.

  Theorem Write_ok : forall a b,
      implements
        (DSpec.Write a b)
        (Write a b)
        (fun w => abstraction (TD.abstraction w))
        (fun w => invariant (TD.abstraction w)).
  Proof.
    intros.
    unfold implements; simpl; intros.
    unfold Write in H.
    repeat step.
    repeat match goal with
           | [ H: io_step (TD.Write _ _ _) _ _ _ |- _ ] =>
             eapply TD.Write_ok in H; simpl in H; safe_intuition
           end.
    safe_intuition;
      hide_fn TD.abstraction; subst;
      try match goal with
      | [ H: invariant _ |- _ ] =>
        pose proof (H a); repeat (simpl_match || deex)
          end.
    unfold TDSpec.upd_disk; destruct matches.
  Qed.

End D.
