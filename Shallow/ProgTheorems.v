Require Import Automation.
Require Import Prog.

Set Implicit Arguments.

(** Here we prove some basic sanity checks on prog and its semantics. *)

Hint Constructors exec.

Theorem can_crash_at_begin : forall T (p: prog3 T) pstate,
    exec p pstate (Crashed pstate).
Proof.
  eauto.
Qed.

Theorem can_crash_at_end : forall T (p: prog3 T) pstate v pstate',
    exec p pstate (Finished v pstate') ->
    exec p pstate (Crashed pstate').
Proof.
  induction p; intros;
    inv_exec;
    eauto.
Qed.

Theorem exec_decidable T (p: prog3 T) pstate :
  { r | let '(v, pstate') := r in
        exec p pstate (Finished v pstate')} + {exec p pstate Failed}.
Proof.
  generalize dependent pstate.
  induction p; simpl; intros.
  - destruct (disk_id i pstate a) eqn:?.
    + left.
      refine (exist _ (_, _) _).
      eapply ExecStepTo; simpl; simpl_match; eauto.
    + right.
      eapply ExecStepFail; simpl; simpl_match; eauto.
  - destruct (disk_id i pstate a) eqn:?.
    + left.
      refine (exist _ (_, _) _).
      eapply ExecStepTo; simpl; simpl_match; eauto.
    + right.
      eapply ExecStepFail; simpl; simpl_match; eauto.
  - left.
    refine (exist _ (_, _) _).
    eapply ExecStepTo; simpl; eauto.
  - destruct (IHp pstate); eauto.
    destruct s as [ [v pstate'] ?].
    specialize (X v).
    destruct (X pstate'); eauto.
    destruct s as [ [v' pstate''] ?].
    left; exists (v', pstate'').
    eauto.
Defined.

(** These are the monad laws

TODO: explain what the monad is and what these monad laws mean (specifically,
we're proving that exec treats programs up to the monad laws as equivalences
between programs).
 *)

Definition exec_equiv T (p p': prog3 T) :=
  forall pstate r, exec p pstate r <-> exec p' pstate r.

Lemma exec_ret : forall T (v:T) pstate r,
    exec (Ret v) pstate r ->
    match r with
    | Finished v' pstate' => v = v' /\ pstate = pstate'
    | Crashed pstate' => pstate = pstate'
    | Failed => False
    end.
Proof.
  intros.
  inv_exec; simpl in *;
    try match goal with
        | [ H: StepTo _ _ = StepTo _ _ |- _ ] =>
          inversion H; subst
        end;
    intuition; try congruence.
Qed.

Ltac cleanup_exec :=
  match goal with
  | [ H: step (Bind _ _) _ = _ |- _ ] =>
    try solve [ simpl in H; inversion H ]
  | [ H: exec (Ret _) _ ?r |- _ ] =>
    first [ is_var r |
            apply exec_ret in H; safe_intuition; subst;
          try solve [ exfalso; apply H ] ]
  end.

Theorem monad_left_id : forall T T' (p: T' -> prog3 T) v,
    exec_equiv (Bind (Ret v) p) (p v).
Proof.
  unfold exec_equiv; split; intros.
  - inv_exec; try cleanup_exec; eauto.
  - eapply ExecBindFinished; eauto.
    eapply ExecStepTo; eauto.
Qed.

Theorem monad_right_id : forall T (p: prog3 T),
    exec_equiv (Bind p (fun v => Ret v)) p.
Proof.
  unfold exec_equiv; split; intros.
  - destruct r; inv_exec; try cleanup_exec; eauto.
    eapply can_crash_at_end; eauto.
  - destruct r; eauto.
Qed.

Lemma exec_bind : forall T T' (p: prog3 T) (p': T -> prog3 T') pstate r,
    exec (Bind p p') pstate r ->
    (exists v pstate', exec p pstate (Finished v pstate') /\
                  exec (p' v) pstate' r) \/
    (exists pstate', exec p pstate (Crashed pstate') /\
                r = Crashed pstate') \/
    (exec p pstate Failed /\
    r = Failed).
Proof.
  intros.
  inv_exec; try simp_stepto; eauto.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("Pstate" . ?Σ) ("pstate" . ?σ) ("pstate'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
