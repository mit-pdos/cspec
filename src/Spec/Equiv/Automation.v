Require Export Spec.ThreadsState.
Require Export Spec.ConcurExec.

Ltac thread_upd_ind p :=
  let ind H := induction H; intros; subst; eauto; NoProc_upd in
  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
    remember (thread_upd ts tid (Proc pp));
    generalize dependent ts;
    generalize dependent p;
    ind H
  | H : exec_till _ _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
    remember (thread_upd ts tid (Proc pp));
    generalize dependent ts;
    generalize dependent p;
    ind H
  end.

Ltac guess_ExecPrefix :=
  match goal with
  | [ H: thread_get _ ?tid' = NoProc |- context[prepend ?tid _ _] ] =>
    ExecPrefix tid tid'
  end.

Ltac solve_ExecEquiv :=
  match goal with
  | [ H: context[thread_get (thread_upd _ ?tid _) ?tid'] |- _ ] =>
    cmp_ts tid' tid; repeat maybe_proc_inv;
    exec_tid_simpl;
    remove_redundant_upds;
    try (solve [ eauto ] ||
         solve [ guess_ExecPrefix ])
  end.

Ltac ExecEquiv p :=
  thread_upd_ind p;
  [ solve_ExecEquiv | .. ].
