Require Import IOstep.
Require Import Automation.

Axiom io_crash : forall T, IO T -> world -> world -> Prop.

Axiom io_crash_init : forall T (p:IO T) w, io_crash p w w.

Axiom io_crash_step : forall T (p:IO T) w r w',
    io_step p w r w' -> io_crash p w w'.

Axiom bind_crash : forall T T' (p: IO T) (p': T -> IO T') w w_c,
    io_crash (Bind p p') w w_c <->
    io_crash p w w_c \/
     (exists v w', io_step p w v w' /\
              io_crash (p' v) w' w_c).

Lemma ret_can_crash : forall T (v:T) w,
    io_crash (Ret v) w w.
Proof.
  intros.
  apply io_crash_init.
Qed.

(* need to assume that crashing at the current step is the only way ret can
crash *)
Axiom ret_crash : forall T (v:T) w w',
    io_crash (Ret v) w w' -> w' = w.

Theorem bind_crash1 : forall T T' (p: IO T) (p': T -> IO T') w w',
    io_crash p w w' ->
    io_crash (Bind p p') w w'.
Proof.
  intros.
  apply bind_crash; eauto.
Qed.

Theorem bind_crash2 : forall T T' (p: IO T) (p': T -> IO T') w v w' w'',
    io_step p w v w' ->
    io_crash (p' v) w' w'' ->
    io_crash (Bind p p') w w''.
Proof.
  intros.
  apply bind_crash; eauto.
Qed.

Definition io_crash_equiv (step1 step2: world -> world -> Prop) :=
  forall w w', step1 w w' <-> step2 w w'.

Ltac step :=
  match goal with
  | [ H: io_crash (Bind _ _) _ _ |- _ ] =>
    eapply bind_crash in H; intuition; repeat deex
  | [ H: io_crash (Ret _) _ _ |- _ ] =>
    eapply ret_crash in H; subst
  | _ => Monad.step
  end.

Module CrashMonad.

  Hint Resolve io_crash_init io_crash_step bind_crash1 bind_crash2.

  Local Ltac t :=
    repeat match goal with
           | |- io_crash_equiv _ _ => split
           | _ => progress intros
           | _ => step
           end; eauto 10.

  Theorem monad_left_id : forall T (v:T) T' (p: T -> IO T'),
      io_crash_equiv (io_crash (Bind (Ret v) p))
                     (io_crash (p v)).
  Proof.
    t.
  Qed.

  Theorem monad_right_id : forall T (p: IO T),
      io_crash_equiv (io_crash (Bind p Ret))
                     (io_crash p).
  Proof.
    t.
  Qed.

  Theorem monad_assoc : forall T (p: IO T)
                          T' (p': T -> IO T')
                          T'' (p'': T' -> IO T''),
      io_crash_equiv (io_crash (Bind (Bind p p') p''))
                     (io_crash (Bind p (fun v => Bind (p' v) p''))).
  Proof.
    t.
  Qed.

End CrashMonad.
