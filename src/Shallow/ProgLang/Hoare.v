(** Crash Hoare Logic specifications *)

(* TODO: document how specifications are structured *)

Require Import Automation.
Require Import Prog.
Require Import ProgTheorems.

Set Implicit Arguments.

(* quadruple is a low-level type; these will appear inside [Specification]s
using record builder syntax, which is already reasonably nice. *)
Record Quadruple T State :=
  Spec {
      pre: Prop;
      post: T -> State -> Prop;
      crash: State -> Prop;
    }.

(** A specification quantifies over ghost state of type A, and gives pre/post
conditions and crash invariant specialized to a particular initial state. (This
is why [pre] above is just a [Prop].) *)
Definition Specification A T State := A -> State -> Quadruple T State.

(* TODO: come up with a good, short name for terms of type Refinement (currently
using [rf], which I'm not too happy with) *)
Record Refinement State :=
  { invariant: world -> Prop;
    abstraction: world -> State }.

Definition prog_spec `(spec: Specification A T State) `(p: prog T)
           (rf: Refinement State) :=
  forall a w,
    let state := abstraction rf w in
    pre (spec a state) ->
    invariant rf w ->
    forall r, exec p w r ->
         match r with
         | Finished v w' => let state' := abstraction rf w' in
                           post (spec a state) v state' /\
                           invariant rf w'
         | Crashed w' => let state' := abstraction rf w' in
                        crash (spec a state) state' /\
                        (* TODO: should this invariant really be here, or should
                        there be a weaker crash refinement defined for the
                        refinement of this specific program? *)
                        invariant rf w'
         end.

(** Hoare double higher-order precondition *)
Definition DoublePre T State :=
  (* initial state *)
  State ->
  (* postcondition *)
  (T -> State -> Prop) ->
  (* crash invariant *)
  (State -> Prop) ->
  Prop.

(** [prog_double] defines correctness in terms of a higher-order precondition.
*)
Definition prog_double `(pre: DoublePre T State) `(p: prog T)
           (rf: Refinement State) :=
  forall w postcond crashinv,
    let state := abstraction rf w in
    pre state postcond crashinv ->
    invariant rf w ->
    forall r, exec p w r ->
         match r with
         | Finished v w' => let state' := abstraction rf w' in
                           postcond v state' /\
                           invariant rf w'
         | Crashed w' => let state' := abstraction rf w' in
                        crashinv state' /\
                        invariant rf w'
         end.

(** [prog_ok] defines correctness by encoding a naturally stated specification
(with separate precondition, postcondition, and crash invariants) into a Hoare
double. *)
Definition prog_ok `(spec: Specification A T State) `(p: prog T)
           (rf: Refinement State) :=
  forall T' (rx: T -> prog T'),
    prog_double
      (fun state postcond crashinv =>
         exists a, pre (spec a state) /\
              (forall r, prog_double
                      (fun state' postcond' crashinv' =>
                         post (spec a state) r state' /\
                         postcond' = postcond /\
                         crashinv' = crashinv)
                      (rx r) rf) /\
              (forall state', crash (spec a state) state' ->
                     crashinv state')) (Bind p rx) rf.

(** We prove a conversion theorem from the Hoare double-based correctness
statement to the more natural quadruple interpretation. This theorem reveals a
subtlety in the double-based encoding: because it assumes the continuation is
safe in any state satisfying the postcondition, it is assumed in the
precondition that the crash invariant (crashinv in the Hoare double) is handled
by the continuation's proof. We cannot make that assumption here when
establishing the crash invariant in the case that [p] crashes just before
finishing, so we explicitly assume that the postcondition implies the crash
invariant. *)
Theorem prog_ok_to_spec : forall `(rf: Refinement State)
                            `(spec: Specification A T State) (p: prog T),
    (forall a w r w',
        let state := abstraction rf w in
        let state' := abstraction rf w' in
        pre (spec a state) ->
        post (spec a state) r state' ->
        crash (spec a state) state' /\
        invariant rf w') ->
    prog_ok spec p rf -> prog_spec spec p rf.
Proof.
  unfold prog_ok, prog_double, prog_spec; intros.
  specialize (H0 _ Ret).
  specialize (H0 w).
  eapply H0; eauto.
  exists a; intuition eauto; subst.
  match goal with
  | [ H: exec (Ret _) _ _ |- _ ] =>
    apply exec_ret in H
  end.
  destruct r1; intuition (subst; eauto).
  eapply H; eauto.
  apply monad_right_id; auto.
Qed.

Theorem prog_spec_to_ok : forall `(rf: Refinement State)
                            `(spec: Specification A T State) (p: prog T),
    prog_spec spec p rf -> prog_ok spec p rf.
Proof.
  unfold prog_ok, prog_double, prog_spec; intros.
  deex.
  match goal with
  | [ H: exec (Bind _ _) _ _ |- _ ] =>
    apply exec_bind in H
  end.
  intuition; repeat deex.
  + eapply H3.
    intuition eauto.
    eapply H in H2; intuition eauto.
    eapply H in H2; intuition eauto.
    auto.
  + eapply H in H2; intuition eauto.
Qed.

Remark crash_invariants_must_handle_pre :
  forall `(rf: Refinement State)
    `(spec: Specification A T State) (p: prog T),
    prog_spec spec p rf ->
    forall a w,
      let state := abstraction rf w in
      pre (spec a state) ->
      invariant rf w ->
      crash (spec a state) state.
Proof.
  unfold prog_spec; intros.
  specialize (H _ _ ltac:(eauto)).
  intuition.
  eapply (H2 (Crashed w)).
  apply can_crash_at_begin.
Qed.

Theorem double_weaken : forall `(rf: Refinement State)
                          T (pre pre': DoublePre T State) (p: prog T),
    prog_double pre' p rf ->
    (forall state postcond crashinv, pre state postcond crashinv ->
                            pre' state postcond crashinv) ->
    prog_double pre p rf.
Proof.
  unfold prog_double at 2; intros.
  eapply H; eauto.
Qed.

Definition spec_impl
           `(spec1: Specification A' T State)
           `(spec2: Specification A T State) :=
  forall a state, pre (spec2 a state) ->
         exists a', pre (spec1 a' state) /\
               (forall v state', post (spec1 a' state) v state' ->
                        post (spec2 a state) v state') /\
               (forall state', crash (spec1 a' state) state' ->
                      crash (spec2 a state) state').

Theorem spec_weaken : forall `(rf: Refinement State)
                        `(spec1: Specification A' T State)
                        `(spec2: Specification A T State)
                        (p: prog T),
    prog_spec spec1 p rf ->
    forall (Himpl: spec_impl spec1 spec2),
      prog_spec spec2 p rf.
Proof.
  unfold prog_spec; intros.
  specialize (Himpl a (abstraction rf w)); intuition.
  repeat deex; intuition eauto.
  specialize (H a' w); intuition.
  match goal with
  | [ r: Result _, H: forall (r: Result _), _ |- _ ] =>
    specialize (H r)
  end; intuition.
  destruct r; intuition eauto.
Qed.

Theorem prog_ok_weaken : forall `(rf: Refinement State)
                        `(spec1: Specification A' T State)
                        `(spec2: Specification A T State)
                        (p: prog T),
    prog_ok spec1 p rf ->
    forall (Himpl: spec_impl spec1 spec2),
      prog_ok spec2 p rf.
Proof.
  unfold prog_ok; intros.
  eapply double_weaken; eauto.
  intros; repeat deex.
  apply Himpl in H0; repeat deex.
  descend; intuition eauto.
  eapply double_weaken; eauto.
  intros; intuition (subst; eauto).
Qed.

Definition ret_ok : forall T (v:T) `(rf: Refinement State),
    prog_ok
      (fun (_:unit) (state:State) =>
         {| pre := True;
            post := fun r state' => r = v /\ state' = state;
            crash := fun state' => False; |})
      (Ret v)
      rf.
Proof.
  unfold prog_ok, prog_double; intros.
  repeat deex; simpl in *.
  inv_exec; eauto.
  eapply H2; eauto.

  specialize (H2 v w' postcond crashinv); intuition.
  specialize (H2 (Crashed w')).
  eapply H2.
  eapply can_crash_at_begin.
Qed.

Theorem double_exec_equiv : forall `(rf: Refinement State)
                              `(pre: DoublePre T State) (p p': prog T),
    exec_equiv p p' ->
    prog_double pre p' rf ->
    prog_double pre p rf.
Proof.
  unfold prog_double; intros.
  eapply H0 in H1; eauto.
  eapply H; eauto.
Qed.

Ltac monad_simpl :=
  repeat match goal with
         | |- prog_double _ (Bind (Ret _) _) _ =>
           eapply double_exec_equiv; [ apply monad_left_id | ]
         | |- prog_double _ (Bind (Bind _ _) _) _ =>
           eapply double_exec_equiv; [ apply monad_assoc | ]
         end.

(** step_prog_with t handles the first program in a bind by applying tactic t *)
Ltac step_prog_with t :=
  match goal with
  | |- prog_double _ _ _ =>
    monad_simpl;
    eapply double_weaken; [ solve [ t ] | ]
  | |- forall _, _ => intros; step_prog_with t
  | |- prog_ok _ _ _ => unfold prog_ok; step_prog_with t
  end.

(** step_prog applies a registered prog_ok theorem (in the prog hint database)
to the first program in a sequence of binds. *)
Ltac step_prog := step_prog_with ltac:(eauto with prog).

(* This notation builds a pattern; use it as [Hint Extern 1 {{ p; _}} => apply
p_ok : prog] to associated p_ok as the specification for the program (pattern).
Such patterns are used by [step_prog] via the prog hint database. *)
Notation "{{ p ; '_' }}" := (prog_double _ (Bind p _) _)
                              (only parsing, at level 0).

(** * begin

This hack lets us do a case-split on the initial state, by adding a no-op to the
beginning of the program and stepping over it. The whole thing could probably be
reduced to a single theorem that appropriately unfolds [prog_double], but we
haven't made this simplification. *)

Definition begin := Ret tt.
Hint Extern 1 {{ begin; _ }} => apply ret_ok : prog.

Lemma begin_prog_ok : forall `(rf: Refinement State)
                        `(spec: Specification A T State)
                        `(p: prog T),
    prog_ok spec (_ <- begin; p) rf ->
    prog_ok spec p rf.
Proof.
  unfold prog_ok, prog_double; intros.
  repeat deex.
  eapply H; eauto.
  eapply monad_assoc.
  unfold begin; apply monad_left_id.
  auto.
Qed.

Ltac intro_begin :=
  intros; apply begin_prog_ok;
  step_prog; simpl;
  repeat match goal with
         | [ |- exists (_:unit), _ ] => exists tt
         | [ u: unit |- _ ] => destruct u
         | [ |- True /\ _ ] => split; [ auto | ]
         | [ |- _ /\ (forall _, False -> _) ] => split; [ | intros; contradiction ]
         | [ |- forall _, _ ] => intros
         end.

(* for programs that are pure the step automation doesn't work, since there is
no bind in the program *)

Theorem ret_prog_ok : forall `(rf: Refinement State)
                        `(spec: Specification A T State) (v:T),
    (forall a state, pre (spec a state) ->
            post (spec a state) v state /\
            crash (spec a state) state) ->
    prog_ok spec (Ret v) rf.
Proof.
  intros.
  unfold prog_ok, prog_double; intros.
  repeat deex.
  eapply H in H0; intuition eauto.
  specialize (H3 v w postcond crashinv); intuition.
  inv_exec.
  eapply H3; eauto.
  intuition eauto.
Qed.
