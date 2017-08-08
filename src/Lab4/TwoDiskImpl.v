Require Import POCS.
Require Import TwoDiskAPI.
Require Import TwoDiskBaseAPI.


Module TwoDisk (b : TwoDiskBaseAPI) <: TwoDiskAPI.

  Definition init := b.init.
  Definition read := b.read.
  Definition write := b.write.
  Definition size := b.size.
  Definition recover := b.recover.

  Definition abstr := b.abstr.

  Ltac inv_step :=
    match goal with
    | [ H: op_step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      repeat sigT_eq;
      safe_intuition
    end.

  Ltac inv_bg :=
    match goal with
    | [ H: bg_failure _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Theorem maybe_holds_stable : forall state state' F0 F1 i,
    get_disk (other i) state ?|= F0 ->
    get_disk i state ?|= F1 ->
    bg_failure state state' ->
    get_disk (other i) state' ?|= F0 /\
    get_disk i state' ?|= F1.
  Proof.
    intros.
    destruct i; inv_bg; simpl in *; eauto.
  Qed.

  Ltac cleanup :=
    repeat match goal with
           | [ |- forall _, _ ] => intros
           | |- _ /\ _ => split; [ solve [ eauto || congruence ] | ]
           | |- _ /\ _ => split; [ | solve [ eauto || congruence ] ]
           | [ H: Working _ = Working _ |- _ ] => inversion H; subst; clear H
           | [ H: bg_failure _ _ |- _ ] =>
             eapply maybe_holds_stable in H;
             [ | solve [ eauto ] | solve [ eauto ] ]; destruct_ands
           | [ H: _ ?|= eq _, H': _ = Some _ |- _ ] =>
                    pose proof (holds_some_inv_eq _ H' H); clear H
           | [ H: ?A * ?B |- _ ] => destruct H
           | [ H: DiskResult _ |- _ ] => destruct H
           | _ => deex
           | _ => destruct_tuple
           | _ => progress unfold pre_step in *
           | _ => progress autounfold in *
           | _ => progress simpl in *
           | _ => progress subst
           | _ => progress safe_intuition
           | _ => solve [ eauto ]
           | _ => congruence
           | _ => inv_step
           | H: context[match ?expr with _ => _ end] |- _ =>
             destruct expr; [ | solve [ repeat cleanup ] ]
           | H: context[match ?expr with _ => _ end] |- _ =>
             destruct expr; [ solve [ repeat cleanup ] | ]
           end.

  Ltac prim :=
    intros;
    eapply proc_spec_weaken; [ eauto | unfold spec_impl ]; eexists;
    intuition eauto; cleanup;
    intuition eauto; cleanup.

  Hint Resolve holds_in_some_eq.
  Hint Resolve holds_in_none_eq.
  Hint Resolve pred_missing.

  Hint Unfold combined_step.


  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eauto.
  Qed.

  Theorem read_ok : forall i a, proc_spec (read_spec i a) (read i a) recover abstr.
  Proof.
    unshelve prim.
    eauto.
  Qed.

  Theorem write_ok : forall i a v, proc_spec (write_spec i a v) (write i a v) recover abstr.
  Proof.
    admit.
  Admitted.

  Theorem size_ok : forall i, proc_spec (size_spec i) (size i) recover abstr.
  Proof.
    unshelve prim.
    eauto.
  Qed.

  Theorem recover_noop : rec_noop recover abstr no_wipe.
  Proof.
    eauto.
  Qed.

End TwoDisk.
