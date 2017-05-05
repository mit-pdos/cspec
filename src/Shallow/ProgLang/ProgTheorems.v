Require Import Automation.
Require Import Prog.

(** Here we prove some basic sanity checks on prog and its semantics. *)

Local Hint Constructors exec.

Theorem can_crash_at_begin : forall `(p: prog opT T) `(step: Semantics opT State) state,
    exec step p state (Crashed state).
Proof.
  induction p; intros; eauto.
Qed.

Theorem can_crash_at_end : forall `(p: prog opT T) `(step: Semantics opT State) state v state',
    exec step p state (Finished v state') ->
    exec step p state (Crashed state').
Proof.
  induction p; intros;
    inv_exec;
    eauto.
Qed.

Local Hint Resolve can_crash_at_begin can_crash_at_end.

(** These are the monad laws

TODO: explain what the monad is and what these monad laws mean (specifically,
we're proving that exec treats programs up to the monad laws as equivalences
between programs).
 *)

Definition exec_equiv `(step: Semantics opT State) T (p: prog opT T) p' :=
  forall state r, exec step p state r <-> exec step p' state r.

Lemma exec_ret : forall T (v:T) `(step: Semantics opT State) state r,
    exec step (Ret v) state r ->
    match r with
    | Finished v' state' => v = v' /\ state = state'
    | Crashed state' => state = state'
    end.
Proof.
  intros.
  inv_exec; intuition.
Qed.

Ltac cleanup_exec :=
  match goal with
  | [ H: exec _ (Ret _) _ ?r |- _ ] =>
    first [ is_var r |
            apply exec_ret in H; safe_intuition; subst ]
  end.

Theorem monad_left_id : forall T T' opT (p: T' -> prog opT T) `(step: Semantics opT State) v,
    exec_equiv step (Bind (Ret v) p) (p v).
Proof.
  unfold exec_equiv; split; intros.
  - inv_exec; try cleanup_exec; eauto.
  - eapply ExecBindFinished; eauto.
Qed.

Theorem monad_right_id : forall `(p: prog opT T) `(step: Semantics opT State),
    exec_equiv step (Bind p (fun v => Ret v)) p.
Proof.
  unfold exec_equiv; split; intros.
  - destruct r; inv_exec; try cleanup_exec; eauto.
  - destruct r; eauto.
Qed.

Theorem monad_assoc : forall `(p1: prog opT T)
                        `(p2: T -> prog opT T')
                        `(p3: T' -> prog opT T'')
                        `(step: Semantics opT State),
    exec_equiv step (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  unfold exec_equiv; split; intros.
  - destruct r; repeat (inv_exec; eauto).
  - destruct r; repeat (inv_exec; eauto).
Qed.

Lemma exec_bind : forall T T' `(p: prog opT T) (p': T -> prog opT T')
                    `(step: Semantics opT State) state r,
    exec step (Bind p p') state r ->
    (exists v state', exec step p state (Finished v state') /\
             exec step (p' v) state' r) \/
    (exists state', exec step p state (Crashed state') /\
           r = Crashed state').
Proof.
  intros.
  inv_exec; eauto.
Qed.

Lemma exec_weaken : forall `(p: prog opT T) `(step: Semantics opT State) (step': Semantics opT State),
    semantics_impl step step' ->
    forall state r, exec step p state r ->
           exec step' p state r.
Proof.
  induction 2; intros; eauto.
Qed.

Theorem rexec_ret : forall `(v:T) `(step: Semantics opT State) `(rec: prog opT R) state r,
  rexec step (Ret v) rec state r ->
  match r with
  | RFinished v' state' => v' = v /\ state' = state
  | Recovered v' state' => exec_recover step rec state v' state'
  end.
Proof.
  intros.
  inversion H; subst;
    inv_exec; eauto.
Qed.

Local Hint Constructors rexec.

Lemma rexec_finish_any_rec : forall `(p: prog opT T)
                               `(rec: prog opT R)
                               `(rec': prog opT R')
                               `(step: Semantics opT State)
                               state v state',
    rexec step p rec state (RFinished v state') ->
    rexec step p rec' state (RFinished v state').
Proof.
  intros.
  inversion H; subst; eauto.
Qed.

Lemma rexec_recover_bind_inv : forall `(p: prog opT T)
                                 `(p': T -> prog opT T')
                                 `(rec: prog opT R)
                                 `(step: Semantics opT State)
                                 state rv state'',
    rexec step (Bind p p') rec state (Recovered rv state'') ->
    rexec step p rec state (Recovered rv state'') \/
    exists v state', rexec step p rec state (RFinished v state') /\
            rexec step (p' v) rec state' (Recovered rv state'').
Proof.
  intros.
  inversion H; subst.
  inv_exec.
  - right.
    descend; intuition eauto.
  - left; eauto.
Qed.

Local Hint Constructors exec_recover.

Lemma exec_recover_bind_inv : forall `(p: prog opT R)
                                `(p': R -> prog opT R')
                                `(step: Semantics opT State)
                                state rv' state'',
    exec_recover step (Bind p p') state rv' state'' ->
    (exists rv state', exec_recover step p state rv state' /\
              exec_recover step (p' rv) state' rv' state'').
Proof.
  induction 1.
  - inv_exec; eauto 10.
  - repeat deex.
    inv_exec; eauto 10.
    (* Oops, there are two paths we can go down - is this theorem false, or do
    we need to generalize the inductive hypothesis? Double checking the
    semantics of [exec Bind] and [exec_recover] didn't reveal any obvious
    problems. *)
    exists v0; descend; intuition eauto.
    Undo.
    exists rv; descend; intuition eauto.
Admitted.

Theorem rexec_rec_bind_inv : forall `(p: prog opT T)
                             `(rec: prog opT R)
                             `(rec': R -> prog opT R')
                             `(step: Semantics opT State)
                             state rv' state'',
    rexec step p (Bind rec rec') state (Recovered rv' state'') ->
    exists rv state', rexec step p rec state (Recovered rv state') /\
             rexec step (Ret tt) (rec' rv) state' (Recovered rv' state'').
Proof.
  intros.
  inversion H; subst.
  eapply exec_recover_bind_inv in H6; repeat deex.
  descend; intuition eauto.
Qed.
