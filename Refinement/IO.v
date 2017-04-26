(* model of an IO monad *)

Require Automation.

Global Set Implicit Arguments.

Axiom IO : Type -> Type.
Axiom Ret : forall T, T -> IO T.
Axiom Bind : forall T T', IO T -> (T -> IO T') -> IO T'.

(* state the IO monad manipulates *)
Axiom world : Type.

Arguments IO T.
Arguments Ret {T} v.
Arguments Bind {T T'} io io'.

Axiom io_step : forall T, IO T -> world -> T -> world -> Prop.

Axiom ret_step : forall T (v:T) w v' w',
    io_step (Ret v) w v' w' <->
    v' = v /\ w' = w.

Lemma ret_does_step : forall T (v:T) w,
    io_step (Ret v) w v w.
Proof.
  intros.
  apply ret_step; eauto.
Qed.

Axiom bind_step : forall T T' (p: IO T) (p': T -> IO T') w v' w'',
    io_step (Bind p p') w v' w'' <->
    (exists v w', io_step p w v w' /\
             io_step (p' v) w' v' w'').

Lemma bind_does_step : forall T T' (p: IO T) (p': T -> IO T') w v w' v' w'',
    io_step p w v w' ->
    io_step (p' v) w' v' w'' ->
    io_step (Bind p p') w v' w''.
Proof.
  intros.
  eapply bind_step; eauto.
Qed.

Definition io_equiv T (step1 step2: world -> T -> world -> Prop) :=
  forall w v w', step1 w v w' <-> step2 w v w'.

Module Monad.

  Import Automation.

  Hint Resolve ret_does_step bind_does_step.

  Local Ltac t :=
    repeat match goal with
           | |- io_equiv _ _ => split
           | [ H: io_step (Bind _ _) _ _ _ |- _ ] =>
             eapply bind_step in H; repeat deex
           | [ H: io_step (Ret _) _ _ _ |- _ ] =>
             eapply ret_step in H; intuition subst
           | _ => progress intros
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
