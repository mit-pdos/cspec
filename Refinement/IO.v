(* model of an IO monad *)

Require Import Automation.

(* We use Coq's implicit arguments feature, where arguments that can be inferred
(for example, types for polymorphic code) do not have to be passed. This option
causes Coq to use some heuristics to automatically make some arguments to
definitions implicit. *)
Global Set Implicit Arguments.

(* [Axiom IO] assumes the existence of programs; an [IO T] should be thought of
as a computation that has some side-effect and then returns a value of type T.
We will assume programs have a semantics (in terms of more opaque things) and
turn IO into a monad here.

Later on we will assume some more primitive [IO T]'s that manipulate disks,
finally using these to write programs that manipulate IO with assumptions about
how the primitives behave.
*)

Axiom IO : forall (T:Type), Type.

Axiom Ret : forall T, T -> IO T.
Axiom Bind : forall T T', IO T -> (T -> IO T') -> IO T'.

(* The opaque state that all code in the IO monad manipulates. *)
Axiom world : Type.

(* io_step p w v w' holds when p can step from w to w' and return v *)
Axiom io_step : forall T, IO T -> world -> T -> world -> Prop.

(** Now we provide the basic monadic combinators in IO and assume that io_step
gives them the desired semantics. *)

(* We have to adjust the automatically determined implicit arguments for Ret and
Bind to match what we'd like, and also set the argument names. *)
Arguments Ret {T} v.
Arguments Bind {T T'} p p'.

Axiom ret_step : forall T (v:T) w v' w',
    io_step (Ret v) w v' w' <->
    v' = v /\ w' = w.

Axiom bind_step : forall T T' (p: IO T) (p': T -> IO T') w v' w'',
    io_step (Bind p p') w v' w'' <->
    (exists v w', io_step p w v w' /\
             io_step (p' v) w' v' w'').

(* For convenience we re-state one direction of the combinator semantics. *)

Lemma ret_does_step : forall T (v:T) w,
    io_step (Ret v) w v w.
Proof.
  intros.
  apply ret_step; eauto.
Qed.

Lemma bind_does_step : forall T T' (p: IO T) (p': T -> IO T') w v w' v' w'',
    io_step p w v w' ->
    io_step (p' v) w' v' w'' ->
    io_step (Bind p p') w v' w''.
Proof.
  intros.
  eapply bind_step; eauto.
Qed.

(* As a consequence of the semantics we've given above, io_step respects the
monad equivalences: for example, Bind p Ret should be equivalent to p, so we
prove that they have the same io_step rules (monad_right_id). *)

Definition io_equiv T (step1 step2: world -> T -> world -> Prop) :=
  forall w v w', step1 w v w' <-> step2 w v w'.

Ltac step :=
  match goal with
  | [ H: io_step (Bind _ _) _ _ _ |- _ ] =>
    eapply bind_step in H; repeat deex
  | [ H: io_step (Ret _) _ _ _ |- _ ] =>
    eapply ret_step in H; safe_intuition; subst
  end.

Module Monad.

  Hint Resolve ret_does_step bind_does_step.

  Local Ltac t :=
    repeat match goal with
           | |- io_equiv _ _ => split
           | _ => progress intros
           | _ => step
           end; eauto 10.

  Theorem monad_left_id : forall T (v:T) T' (p: T -> IO T'),
      io_equiv (io_step (Bind (Ret v) p))
               (io_step (p v)).
  Proof.
    t.
  Qed.

  Theorem monad_right_id : forall T (p: IO T),
      io_equiv (io_step (Bind p Ret))
               (io_step p).
  Proof.
    t.
  Qed.

  Theorem monad_assoc : forall T (p: IO T)
                          T' (p': T -> IO T')
                          T'' (p'': T' -> IO T''),
      io_equiv (io_step (Bind (Bind p p') p''))
               (io_step (Bind p (fun v => Bind (p' v) p''))).
  Proof.
    t.
  Qed.

End Monad.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                           (at level 60, right associativity).
