Require Import Relations.Relation_Operators.
Require Import RelationClasses.

Require Import Automation.
Require Import Prog.

(** Here we prove some basic sanity checks on prog and its semantics. *)

Local Hint Constructors exec.

Theorem can_crash_at_begin : forall `(p: prog T) w,
    can_crash ->
    exec p w (Crashed w).
Proof.
  eauto.
Qed.

Theorem can_crash_at_end : forall `(p: prog T) w v w',
    can_crash ->
    exec p w (Finished v w') ->
    exec p w (Crashed w').
Proof.
  (* This is a slightly harder proof strategy (induction over the programs is
  more straightforward), but this proof doesn't require finite programs! *)
  intros.
  remember (Finished v w').
  induction H0;
    try match goal with
        | [ H: _ = Finished _ _ |- _ ] =>
          inversion H; subst; clear H
        end; eauto.
Qed.

Local Hint Resolve can_crash_at_begin can_crash_at_end.

(** These are the monad laws

TODO: explain what the monad is and what these monad laws mean (specifically,
we're proving that exec treats programs up to the monad laws as equivalences
between programs).
 *)

Definition exec_equiv T (p: prog T) p' :=
  forall w r, exec p w r <-> exec p' w r.

Instance exec_equiv_equiv T : Equivalence (exec_equiv (T:=T)).
Proof.
  constructor; hnf; unfold exec_equiv; intros;
    repeat match goal with
           | [ H: forall (w:world) (r: Result T), _,
                 w: world,
                 r: Result T |- _ ] =>
             specialize (H w r)
           end; intuition.
Qed.

Ltac cleanup_exec :=
  match goal with
  | [ H: exec (Ret _) _ ?r |- _ ] =>
    first [ is_var r |
            apply exec_ret in H; safe_intuition; subst ]
  end.

Theorem monad_left_id : forall T T' (p: T' -> prog T) v,
    exec_equiv (Bind (Ret v) p) (p v).
Proof.
  unfold exec_equiv; split; intros.
  - inv_exec; try cleanup_exec; eauto.
  - eapply ExecBindFinished; eauto.
Qed.

Theorem monad_right_id : forall `(p: prog T),
    exec_equiv (Bind p (fun v => Ret v)) p.
Proof.
  unfold exec_equiv; split; intros.
  - destruct r; inv_exec; try cleanup_exec; eauto.
  - destruct r; eauto.
Qed.

Theorem monad_assoc : forall `(p1: prog T)
                        `(p2: T -> prog T')
                        `(p3: T' -> prog T''),
    exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  unfold exec_equiv; split; intros.
  - destruct r; repeat (inv_exec; eauto).
  - destruct r; repeat (inv_exec; eauto).
Qed.

(** invert a bind execution *)
Lemma exec_bind : forall T T' `(p: prog T) (p': T -> prog T')
                    w r,
    exec (Bind p p') w r ->
    (exists v w', exec p w (Finished v w') /\
             exec (p' v) w' r) \/
    (exists w', exec p w (Crashed w') /\
           r = Crashed w').
Proof.
  intros.
  inv_exec; eauto.
Qed.

Local Hint Constructors rexec.

Theorem rexec_equiv : forall T (p p': prog T) `(rec: prog R) w r,
    exec_equiv p p' ->
    rexec p' rec w r ->
    rexec p rec w r.
Proof.
  intros.
  inv_rexec.
  apply H in H1; eauto.
  apply H in H1; eauto.
Qed.

(* When a program finishes, its recovery procedure is irrelevant. *)
Lemma rexec_finish_any_rec : forall `(p: prog T)
                               `(rec: prog R)
                               `(rec': prog R')
                               w v w',
    rexec p rec w (RFinished v w') ->
    rexec p rec' w (RFinished v w').
Proof.
  intros.
  inversion H; subst; eauto.
Qed.

Lemma rexec_recover_bind_inv : forall `(p: prog T)
                                 `(p': T -> prog T')
                                 `(rec: prog R)
                                 w rv w'',
    rexec (Bind p p') rec w (Recovered rv w'') ->
    rexec p rec w (Recovered rv w'') \/
    exists v w', rexec p rec w (RFinished v w') /\
            rexec (p' v) rec w' (Recovered rv w'').
Proof.
  intros.
  inversion H; subst.
  inv_exec.
  - left; eauto.
  - right.
    descend; intuition eauto.
  - left; eauto.
Qed.

Local Hint Constructors exec_recover.

Arguments clos_refl_trans_1n {A} R _ _.

(** Invert looped recovery execution for a bind in the recovery procedure. The
wment essentially breaks down the execution of recovering with [_ <- p; p']
into three stages:

- First, p runs until it finishes without crashing.
- Next, p' is repeatedly run using p as the recovery procedure, crashing and
  recovering in a loop. The return value in [p' rv] comes from p and is passed
  from iteration to the next, initialized with the run of p in the first step.
- Finally, the computer stops crashing and [p' rv] can run to completion.
 *)
Lemma exec_recover_bind_inv : forall `(p: prog R)
                                `(p': R -> prog R')
                                w rv' w'',
    exec_recover (Bind p p') w rv' w'' ->
    exists rv1 w1, exec_recover p w rv1 w1 /\
                  exists rv2 w2,
                    clos_refl_trans_1n
                      (fun '(rv, w) '(rv', w') =>
                         rexec (p' rv) p w (Recovered rv' w'))
                      (rv1, w1) (rv2, w2) /\
                    exec (p' rv2) w2 (Finished rv' w'').
Proof.
  induction 1.
  - inv_exec; eauto 10 using rt1n_refl.
  - repeat deex.
    inv_exec; eauto 10.
    descend; intuition eauto.
    descend; intuition eauto.
    eapply rt1n_trans; eauto.
    simpl; eauto.
Qed.
