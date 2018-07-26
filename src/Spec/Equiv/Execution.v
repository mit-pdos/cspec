Require Import Spec.ConcurExec.
Require Import Spec.ThreadsState.

Require Import ProofAutomation.
Require Import Helpers.Instances.
Require Import Morphisms.

Section OpSemantics.

  Context {Op:Type -> Type}.
  Context {State:Type}.
  Variable op_step: OpSemantics Op State.

  Local Obligation Tactic := try RelInstance_t.

  (** A strong notion of execution equivalence, independent of semantics *)

  Definition exec_equiv_ts (ts1 ts2 : threads_state Op) :=
    forall (s : State) tr,
      exec op_step s ts1 tr <->
      exec op_step s ts2 tr.

  Global Program Instance exec_equiv_ts_equivalence :
    Equivalence exec_equiv_ts.

  Local Definition exec_equiv_opt (p1 : maybe_proc Op) p2 :=
    forall (ts : threads_state _) tid,
      exec_equiv_ts (ts [[ tid := p1 ]]) (ts [[ tid := p2 ]]).

  Definition exec_equiv `(p1 : proc Op T) (p2 : proc _ T) :=
    exec_equiv_opt (Proc p1) (Proc p2).

  Definition exec_equiv_rx `(p1 : proc Op T) (p2 : proc _ T) :=
    forall TR (rx : T -> proc _ TR),
      exec_equiv (Bind p1 rx) (Bind p2 rx).

  Global Program Instance exec_equiv_opt_equivalence :
    Equivalence exec_equiv_opt.

  Global Program Instance exec_equiv_equivalence :
    Equivalence (@exec_equiv T).

  Global Program Instance exec_equiv_rx_equivalence :
    Equivalence (@exec_equiv_rx T).

  Global Instance thread_upd_exec_equiv_proper :
    Proper (eq ==> eq ==> exec_equiv_opt ==> exec_equiv_ts) (@thread_upd Op).
  Proof.
    intros.
    intros ts0 ts1 H; subst.
    intros tid tid' H'; subst.
    intros o0 o1 H'.

    unfold exec_equiv_ts; split; intros.
    - apply H'; eauto.
    - apply H'; eauto.
  Qed.

  Global Instance Proc_exec_equiv_proper :
    Proper (exec_equiv ==> exec_equiv_opt) (@Proc Op T).
  Proof.
    intros.
    unfold exec_equiv.
    intros ts0 ts1 H; subst.
    eauto.
  Qed.

  Hint Constructors exec_tid.
  Hint Constructors exec_till.

  Hint Extern 1 (exec _ _ _ _ _) =>
  match goal with
  | |- exec_till _ _ _ ?ts _ => first [ is_evar ts; fail 1 | eapply ConcurExec.exec_ts_eq ]
  end : exec.

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

  Theorem exec_equiv_ret_None : forall `(v : T),
      exec_equiv_opt (Proc (Ret v)) NoProc.
  Proof.
    split; intros.
    - ExecEquiv tt.
    - change tr with (prepend tid nil tr).
      eapply ExecOne with (tid := tid).
      autorewrite with t; eauto.
      rewrite mapping_finite; auto.
      econstructor.
      match goal with
      | |- context[S (thread_max ?ts)] =>
        rewrite thread_upd_same_eq with (tid := S (thread_max ts))
      end.
      autorewrite with t; eauto.
      rewrite mapping_finite; eauto.
  Qed.

  Theorem exec_equiv_rx_proof_helper : forall `(p1 : proc Op T) p2,
      (forall tid tid' `(s : State) s' (ts: threads_state _) tr spawned evs `(rx : _ -> proc _ TR) result,
          exec_tid op_step tid s (Bind p1 rx) s' result spawned evs ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exec op_step s (ts [[tid := Proc (Bind p2 rx)]]) (prepend tid evs tr)) ->
      (forall tid tid' `(s : State) s' (ts: threads_state _) tr evs spawned `(rx : _ -> proc _ TR) result,
          exec_tid op_step tid s (Bind p2 rx) s' result spawned evs ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exec op_step s (ts [[tid := Proc (Bind p1 rx)]]) (prepend tid evs tr)) ->
      exec_equiv_rx p1 p2.
  Proof.
    split; intros.
    - ExecEquiv tt.
    - ExecEquiv tt.
  Qed.

  Theorem exec_equiv_rx_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3),
      exec_equiv_rx (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
  Proof.
    split; intros.
    - ExecEquiv p1.
      ExecPrefix tid tid'.
      destruct result0; eauto.
    - ExecEquiv p1.
      ExecPrefix tid tid'.
      destruct result; eauto.
  Qed.

  Theorem exec_equiv_ret_bind : forall `(v : T) `(p : T -> proc Op T'),
      exec_equiv_rx (Bind (Ret v) p) (p v).
  Proof.
    intros.
    eapply exec_equiv_rx_proof_helper; intros; exec_tid_simpl.
    - simpl.
      rewrite thread_upd_same_eq with (tid:=tid') in H2 by eauto.
      eauto.
    - abstract_tr.
      ExecPrefix tid tid'.
      ExecPrefix tid tid'.
      rewrite <- prepend_app; simpl; auto.
  Qed.

  Theorem exec_equiv_bind_ret : forall `(p : proc Op T),
      exec_equiv (Bind p Ret) p.
  Proof.
    unfold exec_equiv; split; intros.

    - ExecEquiv p.
      destruct result0.
      + ExecPrefix tid tid'.
        eapply exec_equiv_ret_None; eauto.
      + ExecPrefix tid tid'.

    - ExecEquiv p.
      destruct result; guess_ExecPrefix.
      eapply exec_equiv_ret_None; eauto.
  Qed.

  Global Instance exec_equiv_rx_to_exec_equiv :
    subrelation (@exec_equiv_rx T) exec_equiv.
  Proof.
    unfold subrelation, exec_equiv_rx; intros.
    rewrite <- exec_equiv_bind_ret with (p := x).
    rewrite <- exec_equiv_bind_ret with (p := y).
    eauto.
  Qed.

  Theorem exec_equiv_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3),
      exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
  Proof.
    intros.
    rewrite exec_equiv_rx_bind_bind; reflexivity.
  Qed.

  Theorem exec_equiv_bind_a : forall `(p : proc Op T) `(p1 : T -> proc _ T') p2,
      (forall x, exec_equiv (p1 x) (p2 x)) ->
      exec_equiv (Bind p p1) (Bind p p2).
  Proof.
    unfold exec_equiv; split; intros.
    - ExecEquiv p.
      ExecPrefix tid tid'.
      destruct result0; eauto.
      eapply H; eauto.

    - ExecEquiv p.
      ExecPrefix tid tid'.
      destruct result0; eauto.
      eapply H; eauto.
  Qed.

  Local Theorem exec_equiv_congruence : forall T (p1 p2: proc Op T) T' (rx1 rx2: T -> proc Op T'),
      exec_equiv_rx p1 p2 ->
      (forall x, exec_equiv_rx (rx1 x) (rx2 x)) ->
      exec_equiv_rx (Bind p1 rx1) (Bind p2 rx2).
  Proof.
    intros.
    unfold exec_equiv_rx; intros.
    repeat rewrite exec_equiv_bind_bind.
    etransitivity.
    eapply H.
    eapply exec_equiv_bind_a; intros.
    eapply H0.
  Qed.

  Theorem exec_equiv_rx_bind_a : forall `(p : proc Op T) `(p1 : T -> proc _ T') p2,
      (forall x, exec_equiv_rx (p1 x) (p2 x)) ->
      exec_equiv_rx (Bind p p1) (Bind p p2).
  Proof.
    intros.
    eapply exec_equiv_rx_proof_helper; intros.
    - exec_tid_inv.
      exec_tid_inv.
      ExecPrefix tid tid'.
      destruct result; eauto.
      eapply H; eauto.
      apply exec_equiv_bind_bind.
      apply exec_equiv_bind_bind in H3.
      eapply exec_equiv_bind_a; intros; eauto; simpl.
      symmetry.
      eapply H; eauto.
    - exec_tid_inv.
      exec_tid_inv.
      ExecPrefix tid tid'.
      destruct result; eauto.
      eapply H; eauto.
      apply exec_equiv_bind_bind.
      apply exec_equiv_bind_bind in H3.
      eapply exec_equiv_bind_a; intros; eauto; simpl.
      eapply H; eauto.
  Qed.

  Theorem exec_equiv_atomicret_ret : forall `(v : T),
      exec_equiv_rx (Atomic (Ret v)) (Ret v).
  Proof.
    intros.
    eapply exec_equiv_rx_proof_helper; intros; exec_tid_simpl.
    - repeat atomic_exec_inv.
      ExecPrefix tid tid'.
    - ExecPrefix tid tid'.
  Qed.

  Theorem exec_equiv_until : forall `(p : option T -> proc Op T) (c : T -> bool) v,
      exec_equiv_rx (Until c p v) (until1 c p v).
  Proof.
    intros.
    eapply exec_equiv_rx_proof_helper; intros.
    - exec_tid_simpl.
      rewrite thread_upd_same_eq with (tid:=tid') in H2 by congruence.
      simpl; eauto.
    - abstract_tr.
      ExecPrefix tid tid'.
      ExecPrefix tid tid'.
      rewrite <- prepend_app; auto.
  Qed.

  Theorem exec_equiv_spawn : forall `(p1 : proc Op T) p2,
      exec_equiv p1 p2 ->
      exec_equiv_rx (Spawn p1) (Spawn p2).
  Proof.
    intros.
    eapply exec_equiv_rx_proof_helper; intros.
    - exec_tid_simpl.
      ExecPrefix tid tid'.
      rewrite thread_upd_ne_comm in * by auto.
      match goal with
      | H : exec_equiv _ _ |- _ =>
        apply H; eauto
      end.
    - exec_tid_simpl.
      ExecPrefix tid tid'.
      rewrite thread_upd_ne_comm in * by auto.
      match goal with
      | H : exec_equiv _ _ |- _ =>
        apply H; eauto
      end.
  Qed.

  Global Instance Bind_exec_equiv_proper :
    Proper (exec_equiv_rx ==>
                          pointwise_relation T exec_equiv_rx ==>
                          @exec_equiv_rx TR) Bind.
  Proof.
    unfold Proper, respectful, pointwise_relation; intros.
    apply exec_equiv_congruence; auto.
  Qed.

  Global Instance Spawn_exec_equiv_proper :
    Proper (@exec_equiv T ==> exec_equiv_rx) Spawn.
  Proof.
    unfold Proper, respectful, pointwise_relation; intros.
    apply exec_equiv_spawn; auto.
  Qed.

  Global Instance exec_proper_exec_equiv :
    Proper (eq ==> exec_equiv_ts ==> eq ==> iff) (@exec Op State op_step).
  Proof.
    unfold Proper, respectful; intros; subst; eauto.
  Qed.

  Global Instance SpawnN_exec_equiv_proper :
      Proper (eq ==> (exec_equiv (T:=T)) ==> exec_equiv_rx) SpawnN.
  Proof.
    unfold Proper, respectful; intros; subst.
    induction y; simpl.
    - reflexivity.
    - rewrite H0.
      setoid_rewrite IHy.
      reflexivity.
  Qed.

End OpSemantics.
