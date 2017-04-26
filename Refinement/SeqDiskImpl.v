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

  Definition invariant (ds:TDSpec.State) :=
    forall a, match TDSpec.disk0 ds a with
         | Some v0 => exists v1, TDSpec.disk1 ds a = Some v1
         | None => TDSpec.disk1 ds a = None
         end.

  (* we need this lemma due to some terrible behavior in congruence:
   https://coq.inria.fr/bugs/show_bug.cgi?id=5394 *)
  Lemma invariant_respects_eq : forall ds ds',
      ds = ds' ->
      invariant ds ->
      invariant ds'.
  Proof.
    intros; subst; auto.
  Qed.

  Hint Resolve invariant_respects_eq.

  Theorem Read_ok : forall a,
      implements
        (DSpec.Read a)
        (io_semantics (Read a))
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
      invariant (TDSpec.Disks (upd d_0 a b) (upd d_1 a b)).
  Proof.
    unfold invariant; simpl; intros.
    destruct (a == a0); unfold equiv, complement in *; subst;
      autorewrite with upd; eauto.
    apply H.
  Qed.

  Hint Resolve invariant_stable_upd.

  Theorem Write_ok : forall a b,
      implements
        (DSpec.Write a b)
        (io_semantics (Write a b))
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
    destruct matches; safe_intuition; subst;
      hide_fn TD.abstraction;
      match goal with
      | [ H: invariant _ |- _ ] =>
        pose proof (H a); repeat (simpl_match || deex)
      end.
    - rewrite TDSpec.get_disk1_upd_d0 in *.
      simpl_match; subst.
      destruct t; simpl.
      intuition eauto.
    - repeat (subst || simpl_match).
      intuition eauto.
  Qed.

End D.
