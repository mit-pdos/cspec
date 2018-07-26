(**
 * This file defines helper theorems and tactics to optimize
 * the code generated through Cspec, by evaluating the layer
 * compilations before extraction.
 *)

Require Import Spec.ConcurProc.
Require Import Spec.ExecSemantics.
Require Import Spec.Equiv.
Require Import Spec.ThreadsState.
Require Import Helpers.ProofAutomation.
Require Import Helpers.ListStuff.
Require Import List.
Require Import Omega.
Require Import Morphisms.


Theorem exec_equiv_ts_thread_from_list' :
  forall Op State (step : OpSemantics Op State) tl1 tl2 tlbase,
    Forall2 (fun ep1 ep2 =>
      exists T p1 p2,
        ep1 = existT _ T p1 /\
        ep2 = existT _ T p2 /\
        exec_equiv step p1 p2) tl1 tl2 ->
    exec_equiv_ts step (thread_from_list (tlbase ++ tl1))
                       (thread_from_list (tlbase ++ tl2)).
Proof.
  induction tl1; destruct tl2; intros; inversion H; clear H.
  - reflexivity.
  - subst; repeat deex.
    specialize (IHtl1 tl2 (tlbase ++ (existT _ T p2 :: nil)) H5); clear H5.
    repeat rewrite <- app_assoc in IHtl1; simpl in *.
    etransitivity; eauto; clear IHtl1.
    match goal with
    | |- exec_equiv_ts _ ?ts _ =>
      specialize (H1 ts (length tlbase))
    end.
    repeat rewrite thread_upd_thread_from_list in H1 by
      ( rewrite app_length; simpl; omega ).
    repeat rewrite list_upd_app with (l1 := tlbase) in H1 by omega.
    replace (length tlbase - length tlbase) with 0 in * by omega.
    simpl in *.
    eauto.
Qed.

Theorem exec_equiv_ts_thread_from_list :
  forall Op State (step : OpSemantics Op State) tl1 tl2,
    Forall2 (fun ep1 ep2 =>
      exists T p1 p2,
        ep1 = existT _ T p1 /\
        ep2 = existT _ T p2 /\
        exec_equiv step p1 p2) tl1 tl2 ->
    exec_equiv_ts step (thread_from_list tl1) (thread_from_list tl2).
Proof.
  intros.
  apply exec_equiv_ts_thread_from_list' with (tlbase := nil).
  eauto.
Qed.

Theorem pointwise_unused :
  forall `(step : OpSemantics Op State) AT RT lhs rhs,
    exec_equiv_rx step lhs rhs ->
    pointwise_relation AT (@exec_equiv_rx _ _ step RT)
      (fun a => lhs) (fun _ => rhs).
Proof.
  unfold pointwise_relation; eauto.
Qed.

Theorem pointwise_used :
  forall `(step : OpSemantics Op State) AT RT lhs rhs,
    (forall a, exec_equiv_rx step (lhs a) (rhs a)) ->
    pointwise_relation AT (@exec_equiv_rx _ _ step RT) lhs rhs.
Proof.
  unfold pointwise_relation; eauto.
Qed.

Theorem exec_equiv_until_once :
  forall T Op State (step : OpSemantics Op State) (p : proc Op T),
    exec_equiv_rx
      step
      (Until (fun _ => true) (fun _ => p) None)
      p.
Proof.
  intros.
  rewrite exec_equiv_until.
  unfold until1.
  unfold exec_equiv_rx.
  intros.
  rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  rewrite exec_equiv_ret_bind.
  reflexivity.
Qed.

Theorem exec_equiv_ts_thread_map_thread_map :
  forall Op1 Op2 Op3 State (step : OpSemantics Op3 State)
         (f : forall T, proc Op1 T -> proc Op2 T)
         (g : forall T, proc Op2 T -> proc Op3 T)
         lhs rhs,
    exec_equiv_ts step lhs
      (thread_map (fun T t => g T (f T t)) rhs) ->
    exec_equiv_ts step lhs
      (thread_map g
        (thread_map f
          rhs)).
Proof.
  intros.
  autorewrite with t.
  eauto.
Qed.
