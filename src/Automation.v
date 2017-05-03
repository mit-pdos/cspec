Require Eqdep.
Require Import EquivDec.

(** * Simplify matches when possible. *)
Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  end.

(* test simpl_match failure when match does not go away *)
Goal forall (vd m: nat -> option nat) a,
    vd a = m a ->
    vd a = match (m a) with
           | Some v => Some v
           | None => None
           end.
Proof.
  intros.
  (simpl_match; fail "should not work here")
  || idtac.
Abort.

Goal forall (vd m: nat -> option nat) a v v',
    vd a =  Some v ->
    m a = Some v' ->
    vd a = match (m a) with
           | Some _ => Some v
           | None => None
           end.
Proof.
  intros.
  simpl_match; now auto.
Abort.

(* hypothesis replacement should remove the match or fail *)
Goal forall (vd m: nat -> option nat) a,
    vd a = m a ->
    m a = match (m a) with
          | Some v => Some v
          | None => None
          end ->
    True.
Proof.
  intros.
  (simpl_match; fail "should not work here")
  || idtac.
Abort.

(** * Find and destruct matches *)
Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
    destruct_matches_in d
  | _ => destruct e eqn:?; intros
  end.

Ltac destruct_all_matches :=
  repeat (try simpl_match;
          try match goal with
              | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
              end);
  subst;
  try congruence;
  auto.

Ltac destruct_nongoal_matches :=
  repeat (try simpl_match;
           try match goal with
           | [ H: context[match ?d with | _ => _ end] |- _ ] =>
             destruct_matches_in d
               end);
  subst;
  try congruence;
  auto.

Ltac destruct_goal_matches :=
  repeat (try simpl_match;
           match goal with
           | [ |- context[match ?d with | _ => _ end] ] =>
              destruct_matches_in d
           end);
  try congruence;
  auto.

Ltac destruct_tuple :=
  match goal with
  | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  | [ |- context[let '(a, b) := ?p in _] ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  end.

Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
Tactic Notation "destruct" "matches" := destruct_goal_matches.

(** * Instantiate existentials (deex) *)

Ltac destruct_ands :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         end.

Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; destruct_ands; subst
  end.

(** * Helpers *)

Ltac descend :=
  repeat match goal with
         | |- exists _, _ => eexists
         end.

Ltac sigT_eq :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.

(* substitute variables that are let bindings (these can be created with [set
(x:=value)] and appear in the context as v := def) *)
Ltac subst_var :=
  repeat match goal with
  | [ v := _ |- _ ] => subst v
  end.

(** * Variants of intuition that do not split the goal. *)

Ltac safe_intuition :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         | [ H: ?P -> _ |- _ ] =>
           lazymatch type of P with
           | Prop => specialize (H ltac:(auto))
           | _ => fail
           end
         end.

Ltac hyp_intuition :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         | [ H: _ \/ _ |- _ ] =>
           destruct H
         end.

(** * Hiding abstraction of lower levels *)

Local Ltac hide_fn_call fn arg :=
  generalize dependent (fn arg); clear arg; intros arg **.

(** hide_fn abstraction will abstract [abstraction t] to an opaque term t; use
 to replace a lower-level abstraction that need not be unfolded. *)
Tactic Notation "hide_fn" constr(fn) :=
  repeat match goal with
         | |- context[fn ?arg] => hide_fn_call fn arg
         | H: context[fn ?arg] |- _ => hide_fn_call fn arg
         end.

(** * Handling == equivalences *)

Ltac is_eq a a' :=
  destruct (a == a'); unfold equiv, complement in *; subst.

(** * Uncategorized *)

Create HintDb false.

Ltac solve_false :=
  solve [ exfalso; eauto with false ].
