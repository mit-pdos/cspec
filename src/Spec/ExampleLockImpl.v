Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import ConcurProc.
Require Import Equiv.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import List.
Require Import Compile.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** Opcodes *)

Inductive opLoT : Type -> Type :=
| TestAndSet : opLoT bool
| Clear : opLoT unit.

Inductive opMidT : Type -> Type :=
| Acquire : opMidT unit
| Release : opMidT unit.

Variable opHiT : Type -> Type.


(** State *)

Definition State := bool.


(** Semantics *)

Inductive lo_step : forall T, opLoT T -> nat -> State -> T -> State -> Prop :=
| LoStepTAS : forall tid v,
  lo_step TestAndSet tid v v true
| LoStepClear : forall tid v,
  lo_step Clear tid v tt false.

Inductive mid_step : forall T, opMidT T -> nat -> State -> T -> State -> Prop :=
| MidStepAcquire : forall tid,
  mid_step Acquire tid false tt true
| MidStepRelease : forall tid v,
  mid_step Release tid v tt false.

Hint Extern 1 (lo_step _ _ _ _ _) => econstructor.
Hint Extern 1 (mid_step _ _ _ _ _) => econstructor.

Ltac step_inv :=
  match goal with
  | H : lo_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  | H : mid_step _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat sigT_eq
  end.


(** Implementations *)

(* XXX being lazy and just calling [OpExec] instead of [Op],
  to avoid shuffling the [OpCall] and [OpRet] symbols *)

CoFixpoint acquire_core : proc opLoT opMidT _ :=
  r <- OpExec TestAndSet;
  if (r == false) then
    Ret tt
  else
    acquire_core.

Definition release_core : proc opLoT opMidT _ :=
  Op Clear.

Definition compile_op T (op : opMidT T) : proc opLoT opMidT T :=
  match op with
  | Acquire => acquire_core
  | Release => release_core
  end.


(** Single-thread correctness, as an experiment *)

Theorem acquire_core_eq :
  acquire_core =
    r <- OpExec TestAndSet;
    if (r == false) then Ret tt else acquire_core.
Proof.
  compile_eq_step.
Qed.

(* General pattern for proving [Acquire]-like implementations:
 *
 * There's a loop, running some operation [op] and bailing out when
 * [op] returns a flag.
 *
 * [op] has two modes of execution: either it has no effect and does
 * not return the flag, or it has the effect matching the high-level
 * operation (e.g., [Acquire] in this example) and returning the flag.
 *
 * The proof considers an iteration of the loop, and shows that either
 * the flag was not returned, and nothing happened (the loop is back to
 * where it was), or the flag was returned and the execution matched the
 * high-level operation (e.g., [Acquire]).
 *)

Theorem traces_match_one_thread_acquire :
  forall R
         (p1rest : _ -> proc opLoT opMidT R)
         (p2rest : _ -> proc opMidT opHiT R),
  (forall x, traces_match_one_thread lo_step mid_step (p1rest x) (p2rest x)) ->
  traces_match_one_thread lo_step mid_step
    (Bind acquire_core p1rest) (Bind (OpExec Acquire) p2rest).
Proof.
  intros.
  unfold traces_match_one_thread, traces_match_ts; intros.

  match goal with
  | H : exec_prefix _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
    remember (thread_upd ts tid (Proc p));
    destruct H as [? H];
    induction H; intros; subst; eauto
  end.

  destruct (tid == 1); subst; autorewrite with t in *.
  * repeat maybe_proc_inv.
    rewrite acquire_core_eq in H1.
    repeat exec_tid_inv.
    repeat step_inv.

    destruct (v == false); subst.

    - apply exec_to_exec_prefix in H2.
      rewrite exec_equiv_ret_bind in H2.
      destruct H2.

      edestruct H; eauto.
      intuition idtac.

      eexists; split.
      eapply ExecPrefixOne with (tid := 1).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.
      eauto.

    - simpl.
      destruct v; try congruence.
      eapply IHexec; eauto.

  * exfalso; eapply thread_empty_inv; eauto.
Qed.

Theorem traces_match_one_thread_release :
  forall R
         (p1rest : _ -> proc opLoT opMidT R)
         (p2rest : _ -> proc opMidT opHiT R),
  (forall x, traces_match_one_thread lo_step mid_step (p1rest x) (p2rest x)) ->
  traces_match_one_thread lo_step mid_step
    (Bind release_core p1rest) (Bind (OpExec Release) p2rest).
Proof.
  intros.
  unfold release_core, Op.
  rewrite exec_equiv_bind_bind.
  rewrite hitrace_incl_opcall.
  rewrite exec_equiv_bind_bind.

  unfold traces_match_one_thread, traces_match_ts; intros.

  match goal with
  | H : exec_prefix _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
    remember (thread_upd ts tid (Proc p));
    destruct H as [? H];
    induction H; intros; subst; eauto
  end.

  destruct (tid == 1); subst; autorewrite with t in *.
  * repeat maybe_proc_inv.
    repeat exec_tid_inv.
    repeat step_inv.

    inversion H2; clear H2; subst.
    destruct (tid == 1); subst; autorewrite with t in *.
    {
      repeat maybe_proc_inv.
      repeat exec_tid_inv.
      edestruct H; eauto.

      intuition idtac.

      eexists; split.
      eapply ExecPrefixOne with (tid := 1).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.
      simpl.
      eauto.
    }

    {
      exfalso; eapply thread_empty_inv; eauto.
    }

    {
      edestruct H; eauto.

      intuition idtac.

      eexists; split.
      eapply ExecPrefixOne with (tid := 1).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.
      simpl.
      eauto.
    }

  * exfalso; eapply thread_empty_inv; eauto.
Qed.


Theorem all_single_thread_traces_match' :
  forall T T' (p1 : proc opLoT opMidT T) (p2 : proc opMidT opHiT T) (p1rest : T -> proc opLoT opMidT T') (p2rest : T -> proc opMidT opHiT T'),
  (forall x, traces_match_one_thread lo_step mid_step (p1rest x) (p2rest x)) ->
  compile_ok compile_op p1 p2 ->
  traces_match_one_thread lo_step mid_step (Bind p1 p1rest) (Bind p2 p2rest).
Proof.
  intros.
  generalize dependent p2rest.
  generalize dependent p1rest.
  induction H0; intros.

  - destruct op.
    + unfold hicall, Op; simpl.
      rewrite exec_equiv_bind_bind with (p1 := OpCallHi _).
      rewrite exec_equiv_bind_bind with (p1 := OpCall _).
      eapply traces_match_one_thread_opcall; intros.

      rewrite exec_equiv_bind_bind with (p1 := acquire_core).
      rewrite exec_equiv_bind_bind with (p1 := OpExec _).
      eapply traces_match_one_thread_acquire; intros.

      eapply traces_match_one_thread_opret; intros.
      eauto.

    + unfold hicall, Op; simpl.
      rewrite exec_equiv_bind_bind with (p1 := OpCallHi _).
      rewrite exec_equiv_bind_bind with (p1 := OpCall _).
      eapply traces_match_one_thread_opcall; intros.

      rewrite exec_equiv_bind_bind with (p1 := release_core).
      rewrite exec_equiv_bind_bind with (p1 := OpExec _).
      eapply traces_match_one_thread_release; intros.

      eapply traces_match_one_thread_opret; intros.
      eauto.

  - repeat rewrite exec_equiv_ret_bind.
    eauto.

  - rewrite exec_equiv_bind_bind.
    rewrite exec_equiv_bind_bind.
    eapply IHcompile_ok.
    intros.
    eapply H1.
    eapply H2.

  - rewrite exec_equiv_ret_bind.

    unfold traces_match_one_thread, traces_match_ts in *; intros.
    eapply H in H0; deex.

    eexists; split.
    eapply ExecPrefixOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eauto.
    autorewrite with t; eauto.
    simpl; eauto.

  - rewrite exec_equiv_ret_bind.

    unfold traces_match_one_thread, traces_match_ts in *; intros.
    eapply H in H0; deex.

    eexists; split.
    eapply ExecPrefixOne with (tid := 1).
      rewrite thread_upd_eq; auto.
      eauto.
    autorewrite with t; eauto.
    simpl; eauto.
Qed.
