Require Import Automation.
Require Import Prog.
Require Import ProofIrrelevance.

(** Here we prove some basic sanity checks on prog and its semantics. *)

Hint Constructors exec.

Theorem can_crash_at_begin : forall T (p: prog T) sigma,
    exec p sigma (Crashed sigma).
Proof.
  eauto.
Qed.

Ltac inj_pair2 :=
  match goal with
  | [ H: existT ?P ?A _ = existT ?P ?A _ |- _ ] =>
    apply inj_pair2 in H; subst
  end.

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ _ |- _ ] =>
    inversion H; subst; clear H;
    repeat inj_pair2
  end.

Theorem can_crash_at_end : forall T (p: prog T) sigma v sigma',
    exec p sigma (Finished v sigma') ->
    exec p sigma (Crashed sigma').
Proof.
  induction p; intros;
    inv_exec;
    eauto.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)