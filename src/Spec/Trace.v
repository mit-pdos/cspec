Require Import ProofAutomation.DependentEq.
Require Import List.

Definition TID := nat.

Inductive event :=
| Event : forall T (v:T), event.
Arguments Event {T} v.

Definition trace := list (TID * event).

Definition thread_tr tid (evs: list event) : trace := map (pair tid) evs.

Theorem thread_tr_app : forall tid evs1 evs2,
    thread_tr tid evs1 ++ thread_tr tid evs2 =
    thread_tr tid (evs1 ++ evs2).
Proof.
  unfold thread_tr; simpl; intros.
  rewrite map_app; auto.
Qed.

Theorem thread_tr_eq : forall tid evs1 evs2,
    thread_tr tid evs1 = thread_tr tid evs2 ->
    evs1 = evs2.
Proof.
  induct evs1.
  - destruct evs2; simpl in *; congruence.
  - destruct evs2; simpl in *; try congruence.
    invert H; eauto.
    f_equal; auto.
Qed.

(* TODO: these are only for backwards compatibility, from when [trace] was an
inductive definition. *)
Definition TraceEmpty : trace := nil.

Definition prepend tid (evs: list event) (tr: trace) : trace :=
  thread_tr tid evs ++ tr.

Theorem prepend_empty_eq : forall tid evs evs',
    prepend tid evs TraceEmpty = prepend tid evs' TraceEmpty ->
    evs = evs'.
Proof.
  unfold prepend; simpl; intros.
  rewrite !app_nil_r in H.
  apply thread_tr_eq in H; auto.
Qed.

Theorem prepend_app : forall (evs1 : list event) evs2 tr tid,
    prepend tid (evs1 ++ evs2) tr = prepend tid evs1 (prepend tid evs2 tr).
Proof.
  unfold prepend; simpl; intros.
  rewrite <- thread_tr_app.
  rewrite app_assoc; auto.
Qed.

Theorem prepend_nil : forall tid tr,
    prepend tid nil tr = tr.
Proof.
  reflexivity.
Qed.
