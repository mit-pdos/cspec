Require Import Helpers.Helpers.

Require List.
Import List.ListNotations.
Open Scope list.

Set Implicit Arguments.

Inductive event :=
| Event : forall T (v : T), event.

Inductive trace :=
| TraceEvent : forall (tid : nat) (ev : event), trace -> trace
| TraceEmpty : trace.


Fixpoint prepend tid (evs : list event) (tr : trace) : trace :=
  match evs with
  | nil => tr
  | e :: evs' =>
    TraceEvent tid e (prepend tid evs' tr)
  end.

Theorem prepend_empty_eq : forall tid evs evs',
    prepend tid evs TraceEmpty = prepend tid evs' TraceEmpty ->
    evs = evs'.
Proof.
  intros.
  generalize dependent evs'.
  induct evs.
  - destruct evs'; simpl in *; congruence.
  - destruct evs'; simpl in *; try congruence.
    invert H.
    f_equal; eauto.
Qed.

Lemma prepend_app : forall `(evs1 : list event) evs2 tr tid,
    prepend tid (evs1 ++ evs2) tr = prepend tid evs1 (prepend tid evs2 tr).
Proof.
  induction evs1; simpl; intros; eauto.
  rewrite IHevs1; eauto.
Qed.

Arguments Event {T}.
