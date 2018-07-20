Require Import ConcurExec.
Require Import Relations.Relation_Operators.
Require Import Morphisms.
Require Import ProofAutomation.
Require Import Helpers.ListStuff.
Require Import Helpers.FinMap.
Require Import Helpers.Instances.
Require Import List.
Require Import Omega.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Section OpSemantics.

  Context {Op:Type -> Type}.
  Context {State:Type}.
  Variable op_step: OpSemantics Op State.

  (** A strong notion of execution equivalence, independent of semantics *)

  Definition exec_equiv_ts (ts1 ts2 : threads_state Op) :=
    forall (s : State) tr,
      exec op_step s ts1 tr <->
      exec op_step s ts2 tr.

  (** A stronger notion of equivalence where number of steps taken must be
    identical *)

  Definition exec_equiv_ts_N n (ts1 ts2: threads_state Op) :=
    forall (s: State) tr,
      exec_till op_step n s ts1 tr <->
      exec_till op_step n s ts2 tr.

  (** A strong notion of equivalence for programs inside atomic sections.
    Basically the same as above, but defined as an underlying [atomic_exec]
    rather than [exec]. *)

  Definition atomic_equiv `(p1 : proc Op T) p2 :=
    forall (s s' : State) r tid evs,
      atomic_exec op_step p1 tid s r s' evs <->
      atomic_exec op_step p2 tid s r s' evs.

  Definition exec_equiv_opt (p1 : maybe_proc Op) p2 :=
    forall (ts : threads_state _) tid,
      exec_equiv_ts (ts [[ tid := p1 ]]) (ts [[ tid := p2 ]]).

  Definition exec_equiv `(p1 : proc Op T) (p2 : proc _ T) :=
    exec_equiv_opt (Proc p1) (Proc p2).

  Definition exec_equiv_rx `(p1 : proc Op T) (p2 : proc _ T) :=
    forall TR (rx : T -> proc _ TR),
      exec_equiv (Bind p1 rx) (Bind p2 rx).

  Local Obligation Tactic := try RelInstance_t.

  Global Program Instance exec_equiv_ts_equivalence :
    Equivalence exec_equiv_ts.

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

  Ltac thread_upd_ind :=
    let ind H := induction H; intros; subst; eauto; NoProc_upd in
    match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      ind H
    | H : exec_till _ _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      ind H
    end.

  (* same as thread_upd_ind, but also generalize the program - this seems
necessary some of the time, and generalizing can break existing proofs *)
  Ltac thread_upd_ind' p :=
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

  Ltac ExecEquiv :=
    thread_upd_ind;
    [ solve_ExecEquiv | .. ].

  (* alternative that uses thread_upd_ind' *)
  Ltac ExecEquiv' p :=
    thread_upd_ind' p;
    [ solve_ExecEquiv | .. ].

  Local Notation exec_p p := (exec_tid _ _ _ p _ _ _ _) (only parsing).

  Theorem exec_equiv_ret_None : forall `(v : T),
      exec_equiv_opt (Proc (Ret v)) NoProc.
  Proof.
    split; intros.
    - ExecEquiv.
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

  Hint Constructors exec_tid.

  Theorem exec_equiv_bind_ret : forall `(p : proc Op T),
      exec_equiv (Bind p Ret) p.
  Proof.
    unfold exec_equiv; split; intros.

    - ExecEquiv' p.
      destruct result0.
      + ExecPrefix tid tid'.
        eapply exec_equiv_ret_None; eauto.
      + ExecPrefix tid tid'.

    - ExecEquiv' p.
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
    - ExecEquiv.
    - ExecEquiv.
  Qed.

  Theorem exec_equiv_ret_bind : forall `(v : T) `(p : T -> proc Op T'),
      exec_equiv_rx (Bind (Ret v) p) (p v).
  Proof.
    intros.
    eapply exec_equiv_rx_proof_helper; intros; exec_tid_simpl.
    - simpl.
      rewrite thread_upd_same_eq with (tid:=tid') in H2 by eauto.
      eauto.
    - rewrite <- app_nil_l with (l := evs).
      rewrite prepend_app.
      ExecPrefix tid tid'.
      ExecPrefix tid tid'.
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

  Theorem exec_equiv_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3),
      exec_equiv_rx (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
  Proof.
    split; intros.
    - ExecEquiv' p1.
      ExecPrefix tid tid'.
      destruct result0; eauto.
    - ExecEquiv' p1.
      ExecPrefix tid tid'.
      destruct result; eauto.
  Qed.

  Theorem exec_equiv_bind_a : forall `(p : proc Op T) `(p1 : T -> proc _ T') p2,
      (forall x, exec_equiv (p1 x) (p2 x)) ->
      exec_equiv (Bind p p1) (Bind p p2).
  Proof.
    unfold exec_equiv; split; intros.
    - ExecEquiv' p.
      ExecPrefix tid tid'.
      destruct result0; eauto.
      eapply H; eauto.

    - ExecEquiv' p.
      ExecPrefix tid tid'.
      destruct result0; eauto.
      eapply H; eauto.
  Qed.

  Theorem exec_equiv_until : forall `(p : option T -> proc Op T) (c : T -> bool) v,
      exec_equiv_rx (Until c p v) (until1 c p v).
  Proof.
    intros.
    eapply exec_equiv_rx_proof_helper; intros.
    - exec_tid_simpl.
      rewrite thread_upd_same_eq with (tid:=tid') in H2 by congruence.
      simpl; eauto.
    - rewrite <- app_nil_l with (l := evs).
      rewrite prepend_app.
      ExecPrefix tid tid'.
      ExecPrefix tid tid'.
  Qed.

  Theorem exec_equiv_congruence : forall T (p1 p2: proc Op T) T' (rx1 rx2: T -> proc Op T'),
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

  Global Instance Bind_exec_equiv_proper :
    Proper (exec_equiv_rx ==>
                          pointwise_relation T exec_equiv_rx ==>
                          @exec_equiv_rx TR) Bind.
  Proof.
    unfold Proper, respectful, pointwise_relation; intros.
    apply exec_equiv_congruence; auto.
  Qed.

  Global Instance exec_proper_exec_equiv :
    Proper (eq ==> exec_equiv_ts ==> eq ==> iff) (@exec Op State op_step).
  Proof.
    unfold Proper, respectful; intros; subst; eauto.
  Qed.

  (** exec_equiv with counter *)

  Definition exec_equiv_N n T (p1 p2: proc Op T) :=
    forall ts tid, exec_equiv_ts_N n (ts [[tid := Proc p1]]) (ts [[tid := Proc p2]]).

  Hint Extern 1 (exec _ _ _ _ _) =>
  match goal with
  | |- exec_till _ _ _ ?ts _ => first [ is_evar ts; fail 1 | eapply ConcurExec.exec_ts_eq ]
  end : exec.

  (* basically the same as ExecPrefix, but applies [ExecTillOne] instead of
[ExecPrefixOne] *)
  Ltac ExecOne tid_arg tid'_arg :=
    eapply ExecTillOne with (tid:=tid_arg) (tid':=tid'_arg);
    autorewrite with t;
    (* need to exclude core for performance reasons *)
    eauto 7 with nocore exec;
    cbv beta iota.

  Hint Constructors exec_till.

  Theorem exec_equiv_N_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3) n,
      exec_equiv_N n (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
  Proof.
    split; intros.
    - ExecEquiv' p1.
      + ExecOne tid tid'.
        destruct result; eauto.
      + ExecOne tid0 tid'.
        abstract_ts; typeclasses eauto 7 with exec.
    - ExecEquiv' p1.
      + ExecOne tid tid'.
        destruct result0; eauto.
      + ExecOne tid0 tid'.
        abstract_ts; typeclasses eauto 7 with exec.
  Qed.


  Global Program Instance atomic_equiv_equivalence :
    Equivalence (@atomic_equiv T).

  Global Instance atomic_equiv_proper :
    Proper (atomic_equiv ==> atomic_equiv ==> iff) (@atomic_equiv T).
  Proof.
    typeclasses eauto.
  Qed.

  Theorem atomic_equiv_ret_bind : forall `(v : T) `(p : T -> proc Op T'),
      atomic_equiv (Bind (Ret v) p) (p v).
  Proof.
    split; intros.
    - atomic_exec_inv.
      invert H9.
    - rewrite <- app_nil_l.
      eauto.
  Qed.

  Theorem atomic_equiv_bind_ret : forall `(p : proc Op T),
      atomic_equiv (Bind p Ret) p.
  Proof.
    split; intros.
    - atomic_exec_inv.
      invert H10.
      rewrite app_nil_r.
      eauto.
    - rewrite <- app_nil_r.
      eauto.
  Qed.

  Theorem atomic_equiv_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3),
      atomic_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
  Proof.
    split; intros.
    - atomic_exec_inv.
      invert H9.
      rewrite <- app_assoc.
      eauto.
    - atomic_exec_inv.
      invert H10.
      rewrite app_assoc.
      eauto.
  Qed.

  Theorem atomic_equiv_bind_congruence : forall T (p1 p2: proc Op T) T' (rx1 rx2: T -> proc Op T'),
      atomic_equiv p1 p2 ->
      (forall x, atomic_equiv (rx1 x) (rx2 x)) ->
      atomic_equiv (Bind p1 rx1) (Bind p2 rx2).
  Proof.
    split; intros; atomic_exec_inv.
    - apply H in H11.
      apply H0 in H12.
      eauto.
    - apply H in H11.
      apply H0 in H12.
      eauto.
  Qed.

  Global Instance Bind_proper_atomic_equiv :
    Proper (atomic_equiv ==>
                         pointwise_relation T atomic_equiv ==>
                         @atomic_equiv TR) Bind.
  Proof.
    unfold Proper, respectful, pointwise_relation; intros.
    apply atomic_equiv_bind_congruence; auto.
  Qed.

  Global Instance Atomic_proper_atomic_equiv :
    Proper (atomic_equiv ==> @exec_equiv_rx T) Atomic.
  Proof.
    intros.
    intros p1 p2 H.
    eapply exec_equiv_rx_proof_helper; intros;
      repeat exec_tid_inv.
    - apply H in H9.
      ExecPrefix tid tid'.
    - apply H in H9.
      ExecPrefix tid tid'.
  Qed.


  (** Trace inclusion for an entire threads_state *)

  Definition trace_incl_ts_s (s s' : State) (ts1 ts2 : threads_state Op) :=
    forall tr,
      exec op_step s ts1 tr ->
      exec op_step s' ts2 tr.

  Definition trace_incl_ts (ts1 ts2 : threads_state Op) :=
    forall (s : State),
      trace_incl_ts_s s s ts1 ts2.

  Global Program Instance trace_incl_ts_s_preorder :
    PreOrder (@trace_incl_ts_s s s).
  Next Obligation.
    hnf; intros.
    eauto.
  Qed.
  Next Obligation.
    unfold trace_incl_ts_s in *; eauto 10.
  Qed.

  Global Program Instance trace_incl_ts_preorder :
    PreOrder trace_incl_ts.

  Global Instance exec_equiv_ts_to_trace_incl_ts :
    subrelation exec_equiv_ts trace_incl_ts.
  Proof.
    unfold subrelation; intros.
    unfold trace_incl_ts, trace_incl_ts_s; intros.
    apply H in H0.
    eauto.
  Qed.

  Theorem trace_incl_ts_s_trans : forall `(s0 : State) s1 s2 `(ts1 : threads_state Op) ts2 ts3,
      trace_incl_ts_s s0 s1 ts1 ts2 ->
      trace_incl_ts_s s1 s2 ts2 ts3 ->
      trace_incl_ts_s s0 s2 ts1 ts3.
  Proof.
    unfold trace_incl_ts_s; intros.
    apply H in H1.
    apply H0 in H1.
    intuition eauto.
  Qed.

  (** Trace inclusion for a single thread *)

  Definition trace_incl_s `(s : State) tid `(p1 : proc Op T) (p2 : proc _ T) :=
    forall ts,
      trace_incl_ts_s s s
                      (ts [[ tid := Proc p1 ]])
                      (ts [[ tid := Proc p2 ]]).

  Definition trace_incl {T} (p1 p2 : proc Op T) :=
    forall (ts : threads_state Op) tid,
      trace_incl_ts
        (ts [[ tid := Proc p1 ]])
        (ts [[ tid := Proc p2 ]]).

  (* natural definition of trace_incl_rx, defined in terms of all executions (that
is, without requiring counters be identical) *)
  Definition trace_incl_rx' {T} (p1 p2 : proc Op T) :=
    forall TF (rx1 rx2: _ -> proc _ TF),
      (forall a, trace_incl (rx1 a) (rx2 a)) ->
      trace_incl (Bind p1 rx1) (Bind p2 rx2).

  Definition trace_incl_ts_N n (ts1 ts2 : threads_state Op) :=
    forall tr s n',
      n' <= n ->
      exec_till op_step n' s ts1 tr ->
      exec op_step s ts2 tr.

  Definition trace_incl_N n {T} (p1 p2 : proc Op T) :=
    forall (ts: threads_state Op) tid,
      trace_incl_ts_N n
                      (ts [[ tid := Proc p1 ]])
                      (ts [[ tid := Proc p2 ]]).

  Definition trace_incl_rx_N n {T} (p1 p2: proc Op T) :=
    forall TF (rx1 rx2 : _ -> proc _ TF) n0,
      n0 <= n ->
      (forall a, trace_incl_N (n0-1) (rx1 a) (rx2 a)) ->
      trace_incl_N n0 (Bind p1 rx1) (Bind p2 rx2).

  Definition trace_incl_rx {T} (p1 p2: proc Op T) :=
    forall n, trace_incl_rx_N n p1 p2.

  Theorem trace_incl_rx'_all_n : forall T (p1 p2: proc Op T),
      (forall n, trace_incl_rx_N n p1 p2) ->
      trace_incl_rx' p1 p2.
  Proof.
    unfold trace_incl_rx', trace_incl, trace_incl_ts, trace_incl_ts_s,
    trace_incl_rx_N, trace_incl_N, trace_incl_ts_N.

    intros.
    apply exec_to_counter in H1; propositional.
    eapply H in H1; eauto.
    intros.
    eapply H0.
    eapply exec_till_to_exec; eauto.
  Qed.

  Theorem trace_incl_rx_all_n : forall T (p1 p2: proc Op T),
      (forall n, trace_incl_rx_N n p1 p2) ->
      trace_incl_rx p1 p2.
  Proof.
    unfold trace_incl_rx; eauto.
  Qed.

  (* this is not true of trace_incl_rx' due to p1 and p2 possibly taking different
numbers of steps *)
  Theorem trace_incl_rx_to_N : forall T (p1 p2: proc Op T),
      trace_incl_rx p1 p2 ->
      forall n, trace_incl_rx_N n p1 p2.
  Proof.
    unfold trace_incl_rx; eauto.
  Qed.

  Theorem trace_incl_all_n : forall T (p1 p2: proc Op T),
      (forall n, trace_incl_N n p1 p2) ->
      trace_incl p1 p2.
  Proof.
    unfold trace_incl_rx, trace_incl, trace_incl_ts, trace_incl_ts_s,
    trace_incl_rx_N, trace_incl_N, trace_incl_ts_N.

    intros.
    apply exec_to_counter in H0; propositional.
    eauto.
  Qed.

  Theorem trace_incl_trace_incl_s : forall T (p1 p2 : proc Op T),
      trace_incl p1 p2 <->
      (forall s tid,
          trace_incl_s s tid p1 p2).
  Proof.
    unfold trace_incl, trace_incl_s, trace_incl_ts.
    split; eauto.
  Qed.

  Global Program Instance trace_incl_s_preorder :
    PreOrder (@trace_incl_s s tid T).

  Global Program Instance trace_incl_preorder :
    PreOrder (@trace_incl T).

  Global Instance exec_equiv_to_trace_incl :
    subrelation (@exec_equiv T) (@trace_incl T).
  Proof.
    unfold subrelation; intros.
    unfold trace_incl, trace_incl_ts, trace_incl_ts_s; intros.
    apply H in H0.
    eauto.
  Qed.

  Global Instance trace_incl_proper :
    Proper (Basics.flip (@trace_incl T) ==>
                        @trace_incl T ==>
                        Basics.impl) (@trace_incl T).
  Proof.
    intros.
    intros p1 p2 H21 p3 p4 H34 H; subst.
    unfold Basics.flip in *.
    etransitivity; eauto.
    etransitivity; eauto.
  Qed.

  Global Instance trace_incl_proper_flip :
    Proper (@trace_incl T ==>
                        Basics.flip (@trace_incl T) ==>
                        Basics.flip Basics.impl) (@trace_incl T).
  Proof.
    intros.
    intros p1 p2 H21 p3 p4 H34 H; subst.
    unfold Basics.flip in *.
    repeat (etransitivity; eauto).
  Qed.

  Global Instance trace_incl_s_proper :
    Proper (Basics.flip (@trace_incl T) ==>
                        @trace_incl T ==>
                        Basics.impl) (@trace_incl_s s tid T).
  Proof.
    intros.
    intros p1 p2 H12 p3 p4 H34 H; subst.
    unfold trace_incl_s, trace_incl_ts_s; intros.
    apply H12 in H0.
    apply H in H0.
    apply H34 in H0.
    eauto.
  Qed.

  Global Instance trace_incl_s_proper_flip :
    Proper (@trace_incl T ==>
                        Basics.flip (@trace_incl T) ==>
                        Basics.flip Basics.impl) (@trace_incl_s s tid T).
  Proof.
    intros.
    intros p1 p2 H12 p3 p4 H34 H; subst.
    unfold trace_incl_s, trace_incl_ts_s; intros.
    apply H12 in H0.
    apply H in H0.
    apply H34 in H0.
    eauto.
  Qed.

  Global Instance trace_incl_s_exec_equiv_proper :
    Proper (exec_equiv ==> exec_equiv ==> iff)
           (@trace_incl_s s tid T).
  Proof.
    intros.
    intros p1 p1' ?.
    intros p2 p2' ?.
    split; intros.
    - unfold trace_incl_s, trace_incl_ts_s; intros.
      apply H in H2.
      apply H1 in H2.
      apply H0 in H2.
      eauto.
    - unfold trace_incl_s, trace_incl_ts_s; intros.
      apply H in H2.
      apply H1 in H2.
      apply H0 in H2.
      eauto.
  Qed.

  Global Instance trace_incl_exec_equiv_proper :
    Proper (exec_equiv ==> exec_equiv ==> iff)
           (@trace_incl T).
  Proof.
    unfold Proper, respectful, trace_incl; intros.
    split; intros.
    rewrite <- H, <- H0; auto.
    rewrite H, H0; auto.
  Qed.

  Lemma trace_incl_ts_s_proof_helper :
    forall `(p1 : proc Op T) (p2 : proc _ T) ts tid s,
      (forall (ts: threads_state _) tid' s0 s' result tr spawned evs,
          exec_others op_step tid s s0 ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec_tid op_step tid s0 p1 s' result spawned evs ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exec op_step s0 (ts [[tid := Proc p2]]) (prepend tid evs tr)) ->
      trace_incl_ts_s s s
                      (ts [[ tid := Proc p1 ]])
                      (ts [[ tid := Proc p2 ]]).
  Proof.
    unfold trace_incl_ts_s.
    intros.
    ExecEquiv.
    ExecPrefix tid0 tid'.
    abstract_ts.
    eapply IHexec; intros; eauto with exec.
    auto with nocore exec.

    Grab Existential Variables.
    all: exact (Ret tt).
  Qed.

  Lemma trace_incl_proof_helper :
    forall `(p1 : proc Op T) p2,
      (forall tid tid' (ts: threads_state _) s s' result tr spawned evs,
          exec_tid op_step tid s p1 s' result spawned evs ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exec op_step s (ts [[tid := Proc p2]]) (prepend tid evs tr)) ->
      trace_incl
                 p1 p2.
  Proof.
    unfold trace_incl, trace_incl_ts.
    intros.

    eapply trace_incl_ts_s_proof_helper.
    eauto.
  Qed.

  Lemma trace_incl_s_proof_helper :
    forall `(p1 : proc Op T) p2 s tid,
      (forall (ts: threads_state _) tid' s0 s' result tr spawned evs,
          exec_others op_step tid s s0 ->
          ts tid' = NoProc ->
          tid <> tid' ->
          exec_tid op_step tid s0 p1 s' result spawned evs ->
          exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                           | inl _ => NoProc
                                                           | inr p' => Proc p'
                                                           end]]) tr ->
          exists tr',
            exec op_step s0 (ts [[tid := Proc p2]]) tr' /\
            prepend tid evs tr = tr') ->
      trace_incl_s s tid p1 p2.
  Proof.
    unfold trace_incl_s.
    intros.

    eapply trace_incl_ts_s_proof_helper.
    intros.
    eapply H in H2; eauto.
    propositional.
  Qed.

  Theorem trace_incl_op :
    forall `(p : T -> proc Op T') op,
      trace_incl
                 (Bind (Call op) p)
                 (Bind (Atomic (Call op)) p).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
    repeat exec_tid_inv.

    ExecPrefix tid tid'.
  Qed.

  Theorem trace_incl_atomize_ret_l :
    forall `(f : T1 -> T2)
      `(p : proc Op T1)
      `(rx : _ -> proc Op TF)
     ,
      trace_incl
                 (Bind (Bind (Atomic p) (fun r => Ret (f r))) rx)
                 (Bind (Atomic (Bind p (fun r => Ret (f r)))) rx).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
    repeat exec_tid_inv.

    eapply trace_incl_ts_s_proof_helper in H2.
    abstract_tr.
    ExecPrefix tid tid'.
    rewrite app_nil_r; auto.

    intros.
    repeat exec_tid_inv.
    rewrite thread_upd_same_eq with (tid:=tid'0) in H6 by congruence.
    assumption.
  Qed.

  Theorem trace_incl_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2',
      (forall x, trace_incl (p2 x) (p2' x)) ->
      trace_incl (Bind p p2) (Bind p p2').
  Proof.
    unfold trace_incl, trace_incl_ts, trace_incl_ts_s.
    intros.

    ExecEquiv' p.
    destruct result0; guess_ExecPrefix.
  Qed.

  Theorem trace_incl_s_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2' s tid,
      (forall s' x,
          exec_any op_step tid s p x s' ->
          trace_incl_s s' tid (p2 x) (p2' x)) ->
      trace_incl_s s tid (Bind p p2) (Bind p p2').
  Proof.
    unfold trace_incl_s, trace_incl_ts_s.
    intros.

    thread_upd_ind' p.

    cmp_ts tid0 tid.
    + repeat maybe_proc_inv.
      exec_tid_inv.
      destruct result0.

      * ExecPrefix tid tid'.
        eauto.
      * ExecPrefix tid tid'.
        eauto.

    + ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec; intros; eauto with exec.
      eauto with exec.
  Qed.

  Theorem trace_incl_N_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2' n,
      (forall x, trace_incl_N (n-1) (p2 x) (p2' x)) ->
      trace_incl_N n (Bind p p2) (Bind p p2').
  Proof.
    unfold trace_incl_N, trace_incl_ts_N.
    intros.

    ExecEquiv' p.
    - destruct result0.
      + epose_proof H.
        2: eassumption.
        omega.

        ExecPrefix tid tid'.
      + epose_proof IHexec_till.
        2: eauto.
        omega.

        ExecPrefix tid tid'.
    - ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec_till; eauto with exec.
      omega.
      auto with exec.
  Qed.

  Theorem trace_incl_N_le :
    forall T (p1 p2 : proc _ T) n1 n2,
      trace_incl_N n2 p1 p2 ->
      n1 <= n2 ->
      trace_incl_N n1 p1 p2.
  Proof.
    repeat ( hnf; intros ).
    eapply H in H2; try omega.
    eauto.
  Qed.

  Global Instance trace_incl_ts_N_reflexive :
    Reflexive (@trace_incl_ts_N n) := RelInstance.
  Proof.
    unfold trace_incl_ts_N; intros.
    eapply exec_till_to_exec; eauto.
  Qed.

  Global Instance trace_incl_N_reflexive :
    Reflexive (@trace_incl_N n T) := RelInstance.

  Global Program Instance trace_incl_rx_preorder :
    PreOrder (@trace_incl_rx T).
  Next Obligation.
    unfold trace_incl_rx, trace_incl_rx_N; intros.
    eapply trace_incl_N_bind_a.
    eauto.
  Qed.
  Next Obligation.
    unfold trace_incl_rx in *.
    repeat (hnf; intros).
    eapply H in H4; try omega.
    apply exec_to_counter in H4; propositional.
    eapply H0 in H4; try omega.
    eauto.
    2: intros; reflexivity.
    reflexivity. reflexivity.
    reflexivity.
    intros; eapply trace_incl_N_le; eauto.
    omega.
  Qed.

  Global Instance Bind_trace_incl_proper_2 :
    Proper (eq ==> pointwise_relation T0 (@trace_incl T) ==>
               @trace_incl T) Bind.
  Proof.
    intros.
    intros p1a p1b H1; subst.
    intros p2a p2b H2.
    eapply trace_incl_bind_a; intros.
    eapply H2.
  Qed.

  Lemma trace_incl_atomic_bind :
    forall `(p1 : proc Op T)
      `(p2 : T -> proc Op T2)
      `(p3 : T2 -> proc Op T3)
     ,
      trace_incl
                 (Bind (Atomic (Bind p1 p2)) p3)
                 (Bind (Bind (Atomic p1) (fun r => Atomic (p2 r))) p3).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
    repeat exec_tid_inv.
    atomic_exec_inv.

    replace (ev1 ++ ev2) with (ev1 ++ ev2 ++ []).
    rewrite ?prepend_app.
    ExecPrefix tid tid'.
    ExecPrefix tid tid'.
    eauto.
    rewrite app_nil_r; auto.
  Qed.

  Lemma trace_incl_atomic :
    forall `(p1 : proc Op T)
      `(p2 : T -> proc Op T2)
     ,
      trace_incl
                 (Bind (Atomic p1) p2)
                 (Bind p1 p2).
  Proof.
    intros.
    eapply trace_incl_proof_helper; intros.
    repeat exec_tid_inv.

    generalize dependent p2.
    generalize dependent tr.

    match goal with
    | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
      induction H; intros; subst
    end.
    - ExecPrefix tid tid'.
    - rewrite thread_upd_same_eq with (tid:=tid') in * by auto.
      rewrite prepend_app.
      rewrite exec_equiv_bind_bind.
      eauto.
    - ExecPrefix tid tid'.
    - abstract_tr.
      ExecPrefix tid tid'.
      eauto.
      rewrite thread_upd_same_eq with (tid:=tid') in * by auto;
        eauto with nocore exec.
  Qed.

  Theorem trace_incl_rx_to_exec :
    forall T (p1 p2: proc _ T)
      (ts: threads_state _) s tid tr,
      trace_incl_rx p1 p2 ->
      exec op_step s (ts [[tid := Proc p1]]) tr ->
      exec op_step s (ts [[tid := Proc p2]]) tr.
  Proof.
    intros.
    eapply exec_equiv_bind_ret in H0.
    eapply exec_equiv_bind_ret.
    eapply exec_to_counter in H0; propositional.
    eapply H in H0; eauto.
    reflexivity.
  Qed.

  Theorem trace_incl_rx_spawn
    : forall T (p1 p2 : proc Op T),
      trace_incl_rx p1 p2 ->
      trace_incl_rx (Spawn p1) (Spawn p2).
  Proof.
    repeat (hnf; intros).
    match goal with
    | H : exec_till _ _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
        generalize dependent ts;
        induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    - repeat maybe_proc_inv.
      repeat exec_tid_inv.
      ExecPrefix tid tid'.

      eapply H1 in H6; try omega.
      rewrite thread_upd_ne_comm in H6 |- * by auto.
      eapply trace_incl_rx_to_exec; eauto.
    - ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec_till; eauto with exec; try omega.
      auto with exec.
  Qed.

  Theorem trace_incl_rx_to_trace_incl :
    forall T (p1 p2 : proc Op T),
      trace_incl_rx p1 p2 ->
      forall `(rx : _ -> proc _ TF),
        trace_incl (Bind p1 rx) (Bind p2 rx).
  Proof.
    repeat (hnf; intros).
    eapply exec_to_counter in H0; propositional.
    eapply H; eauto.
    reflexivity.
  Qed.

  Theorem trace_incl_to_trace_incl_rx :
    forall T (p1 p2 : proc Op T),
      (forall `(rx : _ -> proc _ TF),
          trace_incl (Bind p1 rx) (Bind p2 rx)) ->
      trace_incl_rx p1 p2.
  Proof.
    repeat (hnf; intros).
    assert (trace_incl_rx p1 p1) by reflexivity.
    eapply H4 in H3; [ | reflexivity | eassumption | omega ].
    eapply H; eauto.
  Qed.

  Theorem trace_incl_N_ret_bind :
    forall `(v : T) TF (rx1 rx2 : _ -> proc _ TF) n,
      (forall a, trace_incl_N (n - 1) (rx1 a) (rx2 a)) ->
      trace_incl_N n (Bind (Ret v) rx1) (Bind (Ret v) rx2).
  Proof.
    repeat (hnf; intros).
    ExecEquiv.
    + replace (S n - 1) with n in * by omega.
      eapply H in H4; try omega.
      ExecPrefix tid tid'.
      eauto.
    + ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec_till; eauto with exec.
      omega.
      auto with exec.
  Qed.

  Theorem trace_incl_rx_N_le :
    forall T (p1 p2 : proc _ T) n1 n2,
      trace_incl_rx_N n2 p1 p2 ->
      n1 <= n2 ->
      trace_incl_rx_N n1 p1 p2.
  Proof.
    repeat ( intro; intros ).
    eapply H in H4.
    eassumption.
    3: reflexivity.
    omega.
    intros.
    eapply trace_incl_N_le; eauto.
    omega.
  Qed.

  Theorem trace_incl_rx_until_helper :
    forall T (p1 p2 : option T -> proc Op T)
      (c : T -> bool) n v,
      (forall v', trace_incl_rx_N (n-1) (p1 v') (p2 v')) ->
      trace_incl_rx_N n (Until c p1 v) (Until c p2 v).
  Proof.
    induction n; intros.

    - intro; intros.
      intro; intros.
      intro; intros.
      match goal with
      | H : exec_till _ _ _ _ _ |- _ =>
        invert H; eauto
      end.
      exfalso; omega.

    - intro; intros.
      intro; intros.
      intro; intros.
      match goal with
      | H : exec_till _ _ _ _ _ |- _ =>
        invert H; eauto; NoProc_upd
      end.

      cmp_ts tid0 tid.

      + repeat maybe_proc_inv.
        repeat exec_tid_inv.

        unfold until1 in *.
        lazymatch goal with
        | H : exec_till _ _ _ _ _ |- _ =>
          eapply exec_equiv_N_bind_bind in H
        end.

        replace (S n - 1) with (n) in * by omega.

        match goal with
        | H : exec_till _ _ _ _ _,
              H' : forall _, trace_incl_rx_N _ _ _ |- _ =>
          eapply H' in H; try omega
        end.

        ExecPrefix tid tid'.
        unfold until1.
        rewrite exec_equiv_bind_bind.
        eassumption.
        instantiate (1 := n1); omega.

        simpl; intros.
        destruct (c a).
        * eapply trace_incl_N_ret_bind; intros.
          eapply trace_incl_N_le; eauto. omega.

        * repeat ( intro; intros ).
          eapply IHn.
          intros. eapply trace_incl_rx_N_le; eauto; omega.
          4: eassumption.
          3: reflexivity.
          omega.
          intros; eapply trace_incl_N_le; eauto; omega.

        * auto.

      + ExecPrefix tid0 tid'.
        rewrite ConcurExec.thread_upd_abc_to_cab in * by auto.
        eapply IHn with (n0:=n1) (n':=n1) (rx1:=rx1); intros; try omega; eauto.
        eapply trace_incl_rx_N_le; eauto; omega.
        eapply trace_incl_N_le; eauto; omega.
  Qed.

  Theorem trace_incl_rx_until :
    forall T (p1 p2 : option T -> proc Op T)
      (c : T -> bool) v,
      (forall v', trace_incl_rx (p1 v') (p2 v')) ->
      trace_incl_rx (Until c p1 v) (Until c p2 v).
  Proof.
    repeat ( intro; intros ).
    eapply trace_incl_rx_until_helper in H3.
    5: reflexivity.
    eassumption.
    intros. eapply H.
    reflexivity.
    intros; eapply trace_incl_N_le; eauto; omega.
  Qed.

End OpSemantics.

(** Correspondence between different layers *)

Definition traces_match_ts {opLoT opMidT State} lo_step hi_step
           (ts1 : threads_state opLoT)
           (ts2 : threads_state opMidT) :=
  forall (s : State) tr1,
    exec lo_step s ts1 tr1 ->
    exec hi_step s ts2 tr1.

Global Instance traces_match_ts_proper :
  Proper (@trace_incl_ts opLoT State lo_step ==>
                         @exec_equiv_ts opMidT State hi_step ==>
                         Basics.flip Basics.impl)
         (@traces_match_ts opLoT opMidT State lo_step hi_step).
Proof.
  intros.
  intros ts1 ts1' H1.
  intros ts2 ts2' H2.
  unfold Basics.flip, Basics.impl.
  unfold traces_match_ts; intros.
  apply H1 in H0.
  apply H in H0.
  apply H2 in H0.
  eauto.
Qed.
