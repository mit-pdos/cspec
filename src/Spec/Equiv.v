Require Import ConcurExec.
Require Import Relations.Relation_Operators.
Require Import Morphisms.
Require Import ProofAutomation.
Require Import Helpers.ListStuff.
Require Import Helpers.FinMap.
Require Import List.
Require Import Omega.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** A strong notion of execution equivalence, independent of semantics *)

Definition exec_equiv_ts {Op} (ts1 ts2 : threads_state Op) :=
  forall State op_step (s : State) tr,
    exec op_step s ts1 tr <->
    exec op_step s ts2 tr.

Definition exec_equiv_opt `(p1 : maybe_proc Op) p2 :=
  forall (ts : threads_state _) tid,
    exec_equiv_ts (ts [[ tid := p1 ]]) (ts [[ tid := p2 ]]).

Definition exec_equiv `(p1 : proc Op T) (p2 : proc _ T) :=
  exec_equiv_opt (Proc p1) (Proc p2).

Definition exec_equiv_rx `(p1 : proc Op T) (p2 : proc _ T) :=
  forall TR (rx : T -> proc _ TR),
    exec_equiv (Bind p1 rx) (Bind p2 rx).

Instance exec_equiv_ts_equivalence :
  Equivalence (@exec_equiv_ts Op).
Proof.
  split.
  - firstorder.
  - unfold Symmetric, exec_equiv_ts; intros.
    split; intros; apply H; eauto.
  - unfold Transitive, exec_equiv_ts; intros.
    split; intros.
    + apply H0. apply H. eauto.
    + apply H. apply H0. eauto.
Qed.

Instance exec_equiv_opt_equivalence :
  Equivalence (@exec_equiv_opt Op).
Proof.
  split.
  - unfold exec_equiv_opt, Reflexive; intros.
    reflexivity.
  - unfold exec_equiv_opt, Symmetric; intros.
    symmetry. eauto.
  - intros t1 t2 t3.
    unfold exec_equiv; split; intros.
    + eapply H in H1; eauto.
      eapply H0 in H1.
      eauto.
    + eapply H; eauto.
      eapply H0; eauto.
Qed.

Instance exec_equiv_equivalence :
  Equivalence (@exec_equiv Op T).
Proof.
  unfold exec_equiv.
  split.
  - intro t.
    reflexivity.
  - unfold Symmetric, exec_equiv_opt; intros.
    symmetry. eauto.
  - unfold Transitive; intros.
    etransitivity; eauto.
Qed.

Instance exec_equiv_rx_equivalence :
  Equivalence (@exec_equiv_rx Op T).
Proof.
  unfold exec_equiv_rx.
  split.
  - intro t.
    reflexivity.
  - unfold Symmetric, exec_equiv_opt; intros.
    symmetry. eauto.
  - unfold Transitive; intros.
    etransitivity; eauto.
Qed.

Instance thread_upd_exec_equiv_proper :
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

Instance Proc_exec_equiv_proper :
  Proper (exec_equiv ==> exec_equiv_opt) (@Proc Op T).
Proof.
  intros.
  unfold exec_equiv.
  intros ts0 ts1 H; subst.
  eauto.
Qed.

Lemma thread_upd_aba : forall Op (ts: threads_state Op) tid1 tid2 p1 p2 p3,
    tid1 <> tid2 ->
    ts [[tid1 := p1]] [[tid2 := p2]] [[tid1 := p3]] =
    ts [[tid1 := p3]] [[tid2 := p2]].
Proof.
  intros.
  rewrite thread_upd_ne_comm by auto.
  autorewrite with t; auto.
Qed.

Lemma thread_upd_aba' :
  forall Op (ts: threads_state Op) tid1 tid2 p1 p2 p3,
    tid1 <> tid2 ->
    ts [[tid1 := p1]] [[tid2 := p2]] [[tid1 := p3]] =
    ts [[tid2 := p2]] [[tid1 := p3]].
Proof.
  intros.
  rewrite thread_upd_aba by congruence.
  rewrite thread_upd_ne_comm by auto.
  auto.
Qed.

Lemma thread_spawn_none :
  forall Op (ts: threads_state Op) T (p: proc Op T) tid tid' ,
    tid <> tid' ->
    ts tid' = NoProc ->
    ts [[tid := Proc p]] [[tid' := NoProc]] =
    ts [[tid := Proc p]].
Proof.
  intros.
  rewrite thread_upd_same_eq; auto.
  autorewrite with t; auto.
Qed.

Hint Rewrite thread_spawn_none using congruence : t.

Lemma thread_upd_abc_to_cab :
  forall Op (ts: threads_state Op) tid1 tid2 tid3 p1 p2 p3,
    tid1 <> tid2 ->
    tid1 <> tid3 ->
    ts [[tid1 := p1]] [[tid2 := p2]] [[tid3 := p3]] =
    ts [[tid2 := p2]] [[tid3 := p3]] [[tid1 := p1]].
Proof.
  intros.
  rewrite thread_upd_ne_comm with (tid := tid1) (tid' := tid2) by congruence.
  rewrite thread_upd_ne_comm with (tid := tid1) (tid' := tid3) by congruence.
  auto.
Qed.

Ltac NoProc_upd :=
  repeat lazymatch goal with
         | [ H: thread_get (_ [[?tid := Proc _]]) ?tid' = NoProc |- _ ] =>
           cmp_ts tid tid';
           [ solve [ maybe_proc_inv ] | ]
         | _ => idtac
         end.

(* the ExecPrefix tactic solves exec goals by splitting them into one
execution step and leaving the exec for [auto] *)

(* copy some basic hints from core *)
Hint Extern 2 (_ <> _) => simple apply not_eq_sym; trivial : exec.
Hint Extern 2 (_ = _) => simple apply eq_sym : exec.
Hint Resolve eq_refl : exec.

Lemma thread_upd_other_eq : forall Op (ts:threads_state Op)
                              tid T (p: proc _ T) tid' T' (p': proc _ T'),
    tid' <> tid ->
    ts tid' = Proc p ->
    ts [[tid := Proc p']] tid' = Proc p.
Proof.
  intros.
  autorewrite with t.
  auto.
Qed.

Lemma thread_upd_spawn_delay :
  forall Op (ts: threads_state Op) tid T (p: proc _ T) tid' spawned tid'' p',
    tid'' <> tid ->
    tid <> tid' ->
    ts [[tid := Proc p]] [[tid' := spawned]] [[tid'' := p']] =
    ts [[tid' := spawned]] [[tid'' := p']] [[tid := Proc p]].
Proof.
  intros.
  apply thread_upd_abc_to_cab; auto.
Qed.

Hint Resolve thread_upd_other_eq : exec.
Hint Resolve thread_upd_spawn_delay : exec.
Hint Resolve thread_upd_ne_comm : exec.
Hint Constructors exec_tid atomic_exec : exec.

Hint Extern 1 (exec _ _ _ _) =>
match goal with
| |- exec _ _ ?ts _ => first [ is_evar ts; fail 1 | eapply ConcurExec.exec_ts_eq ]
end : exec.

Ltac ExecPrefix tid_arg tid'_arg :=
  eapply ExecPrefixOne with (tid:=tid_arg) (tid':=tid'_arg);
  autorewrite with t;
  (* need to exclude core for performance reasons *)
  eauto 7 with nocore exec;
  cbv beta iota.

Theorem exec_equiv_ret_None : forall Op `(v : T),
  @exec_equiv_opt Op (Proc (Ret v)) NoProc.
Proof.
  split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid tid0.
    * repeat maybe_proc_inv;
        repeat exec_tid_inv;
        simpl;
        eauto.
    * ExecPrefix tid0 tid'.
      abstract_ts.
      eapply IHexec; eauto with exec.
      rewrite thread_upd_abc_to_cab; auto.

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

Hint Rewrite thread_upd_aba' using congruence : t.

Theorem exec_equiv_bind_ret : forall `(p : proc Op T),
  exec_equiv (Bind p Ret) p.
Proof.
  unfold exec_equiv; split; intros.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst; eauto
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      exec_tid_inv.

      cmp_ts tid tid';
        repeat maybe_proc_inv.

      destruct result0.
      {
        ExecPrefix tid tid'.
        eapply exec_equiv_ret_None; eauto.
      }

      {
        ExecPrefix tid tid'.
      }

    * cmp_ts tid tid';
        repeat maybe_proc_inv.

      ExecPrefix tid0 tid'.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      destruct result.
      {
        ExecPrefix tid tid'.
        eapply exec_equiv_ret_None; eauto.
      }

      {
        ExecPrefix tid tid'.
      }

    * ExecPrefix tid0 tid'.
Qed.

Instance exec_equiv_rx_to_exec_equiv :
  subrelation (@exec_equiv_rx Op T) exec_equiv.
Proof.
  unfold subrelation, exec_equiv_rx; intros.
  rewrite <- exec_equiv_bind_ret with (p := x).
  rewrite <- exec_equiv_bind_ret with (p := y).
  eauto.
Qed.

Lemma thread_upd_other_and_spawn_eq :
  forall Op (ts:threads_state Op)
    tid T (p: proc _ T) tid' spawned tid'' T' (p': proc _ T'),
    tid' <> tid'' ->
    tid <> tid'' ->
    ts tid'' = Proc p ->
    ts [[tid := Proc p']] [[tid' := spawned]] tid'' = Proc p.
Proof.
  intros.
  autorewrite with t; auto.
Qed.

Theorem exec_equiv_rx_proof_helper : forall `(p1 : proc Op T) p2,
    (forall tid tid' `(s : State) s' op_step (ts: threads_state _) tr spawned evs `(rx : _ -> proc _ TR) result,
        exec_tid op_step tid s (Bind p1 rx) s' result spawned evs ->
        ts tid' = NoProc ->
        tid <> tid' ->
        exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                                                | inl _ => NoProc
                                                                | inr p' => Proc p'
                                                                end]]) tr ->
        exec op_step s (ts [[tid := Proc (Bind p2 rx)]]) (prepend tid evs tr)) ->
    (forall tid tid' `(s : State) s' op_step (ts: threads_state _) tr evs spawned `(rx : _ -> proc _ TR) result,
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
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      eauto.

    * ExecPrefix tid0 tid'.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      eauto.
    * ExecPrefix tid0 tid'.
Qed.

Theorem exec_equiv_ret_bind : forall `(v : T) `(p : T -> proc Op T'),
  exec_equiv_rx (Bind (Ret v) p) (p v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv; simpl.
    rewrite thread_upd_same_eq with (tid:=tid') in H2 by eauto.
    eauto.
  - rewrite <- app_nil_l with (l := evs).
    rewrite prepend_app.
    ExecPrefix tid tid'.
    ExecPrefix tid tid'.
Qed.

Theorem exec_equiv_atomicret_bind : forall `(v : T) `(p : T -> proc Op T'),
  exec_equiv_rx (Bind (Atomic (Ret v)) p) (p v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv.
    repeat atomic_exec_inv.
    rewrite thread_upd_same_eq with (tid:=tid') in H2 by eauto.
    eauto.
  - rewrite <- app_nil_l with (l := evs).
    rewrite prepend_app.
    ExecPrefix tid tid'.
    ExecPrefix tid tid'.
Qed.

Theorem exec_equiv_atomicret_ret : forall Op `(v : T),
  @exec_equiv_rx Op _ (Atomic (Ret v)) (Ret v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv.
    repeat atomic_exec_inv.
    rewrite thread_upd_same_eq with (tid:=tid') in H2 by eauto.
    ExecPrefix tid tid'.
    rewrite thread_upd_same_eq with (tid:=tid') by eauto; eauto.
  - repeat exec_tid_inv.
    ExecPrefix tid tid'.
Qed.

Theorem exec_equiv_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3),
  exec_equiv_rx (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.
      exec_tid_inv.
      ExecPrefix tid tid'.

      destruct result0; eauto.

    * ExecPrefix tid0 tid'.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.

      ExecPrefix tid tid'.

      destruct result; eauto.

    * ExecPrefix tid0 tid'.
Qed.

Theorem exec_equiv_norx_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3),
  exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  intros.
  rewrite exec_equiv_bind_bind.
  reflexivity.
Qed.

Theorem exec_equiv_bind_a : forall `(p : proc Op T) `(p1 : T -> proc _ T') p2,
  (forall x, exec_equiv (p1 x) (p2 x)) ->
  exec_equiv (Bind p p1) (Bind p p2).
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      exec_tid_inv.
      ExecPrefix tid tid'.

      destruct result0; eauto.
      eapply H. eauto.

    * ExecPrefix tid0 tid'.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      exec_tid_inv.
      ExecPrefix tid tid'.

      destruct result0; eauto.
      eapply H. eauto.

    * ExecPrefix tid0 tid'.
Qed.

Theorem exec_equiv_bind_bind' : forall `(p1 : proc Op T1) `(p2 : T1 -> proc _ T2) `(p3 : T1 -> T2 -> proc _ T3),
  exec_equiv_rx (Bind p1 (fun x => Bind (p2 x) (p3 x)))
             (Bind (Bind p1 (fun x => Bind (p2 x) (fun y => Ret (x, y))))
                   (fun p => p3 (fst p) (snd p))).
Proof.
  unfold exec_equiv_rx; intros.
  repeat rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  repeat rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  rewrite exec_equiv_ret_bind; simpl.
  reflexivity.
Qed.

Theorem exec_equiv_until : forall `(p : option T -> proc Op T) (c : T -> bool) v,
  exec_equiv_rx (Until c p v) (until1 c p v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv.
    rewrite thread_upd_same_eq with (tid:=tid') in H2 by congruence.
    simpl; eauto.
  - rewrite <- app_nil_l with (l := evs).
    rewrite prepend_app.
    ExecPrefix tid tid'.
    ExecPrefix tid tid'.
Qed.

Theorem exec_equiv_until_once : forall Op `(p : proc Op T),
  exec_equiv_rx (Until (fun _ => true) (fun _ => p) None) p.
Proof.
  intros.
  rewrite exec_equiv_until.
  unfold until1.
  destruct (Bool.bool_dec true true); try congruence.
  unfold exec_equiv_rx; intros.
  rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  rewrite exec_equiv_ret_bind.
  reflexivity.
Qed.

Instance Bind_exec_equiv_proper :
  Proper (exec_equiv_rx ==>
          pointwise_relation T exec_equiv_rx ==>
          @exec_equiv_rx Op TR) Bind.
Proof.
  unfold exec_equiv_rx; intros.
  intros p1a p1b H1; intros.
  intros p2a p2b H2; intros.
  repeat rewrite exec_equiv_bind_bind.
  etransitivity.
  eapply H1.
  eapply exec_equiv_bind_a; intros.
  eapply H2.
Qed.

Theorem exec_equiv_ts_upd_same : forall `(ts : threads_state Op) p tid,
  ts [[ tid ]] = p ->
  exec_equiv_ts ts (ts [[ tid := p ]]).
Proof.
  intros.
  autorewrite with t; reflexivity.
Qed.

Instance exec_proper_exec_equiv :
  Proper (eq ==> eq ==> exec_equiv_ts ==> eq ==> iff) (@exec Op State).
Proof.
  intros.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  apply H.
Qed.

Theorem exec_equiv_rx_bind_ret : forall `(p : proc Op T),
  exec_equiv_rx (Bind p Ret) p.
Proof.
  unfold exec_equiv_rx; intros.
  rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  rewrite exec_equiv_ret_bind.
  reflexivity.
Qed.

(** exec_equiv with counter *)

Definition exec_equiv_ts_N n Op (ts1 ts2: threads_state Op) :=
  forall State op_step (s: State) tr,
    exec_till op_step n s ts1 tr <->
    exec_till op_step n s ts2 tr.

Definition exec_equiv_N n Op T (p1 p2: proc Op T) :=
  forall ts tid, exec_equiv_ts_N n (ts [[tid := Proc p1]]) (ts [[tid := Proc p2]]).

Definition exec_equiv_rx_N n `(p1: proc Op T) (p2: proc _ T) :=
  forall TR (rx: T -> proc _ TR),
    exec_equiv_N n (Bind p1 rx) (Bind p2 rx).

Theorem exec_equiv_N_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3) n,
  exec_equiv_N n (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  split; intros.
    - match goal with
    | H : exec_till _ _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.
      (* ExecOne tid tid'.

      destruct result; eauto. *)
      admit.

    * (* ExecOne tid0 tid'. *)
      admit.

    * constructor.

  - match goal with
    | H : exec_till _ _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst; eauto; NoProc_upd
    end.

    cmp_ts tid0 tid.
    * repeat maybe_proc_inv.
      exec_tid_inv.

      (* ExecOne tid tid'.

      cbv beta iota.
      destruct result0; eauto. *)
      admit.

    * (* ExecOne tid0 tid'. *)
      admit.
Admitted.

(** A strong notion of equivalence for programs inside atomic sections.
    Basically the same as above, but defined as an underlying [atomic_exec]
    rather than [exec]. *)

Definition atomic_equiv `(p1 : proc Op T) p2 :=
  forall State op_step (s s' : State) r tid evs,
    atomic_exec op_step p1 tid s r s' evs <->
    atomic_exec op_step p2 tid s r s' evs.

Instance atomic_equiv_equivalence :
  Equivalence (@atomic_equiv Op T).
Proof.
  split.
  - firstorder.
  - unfold Symmetric, atomic_equiv; intros.
    split; intros; apply H; eauto.
  - unfold Transitive, exec_equiv_ts; intros.
    split; intros.
    + apply H0. apply H. eauto.
    + apply H. apply H0. eauto.
Qed.

Instance atomic_equiv_proper :
  Proper (atomic_equiv ==> atomic_equiv ==> iff) (@atomic_equiv Op T).
Proof.
  intros.
  intros ? ? ?.
  intros ? ? ?.
  split; intros.
  - symmetry.
    etransitivity; eauto.
    symmetry.
    etransitivity; eauto.
  - etransitivity; eauto.
    etransitivity; eauto.
    symmetry; eauto.
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

Theorem atomic_equiv_bind_a : forall `(p : proc Op T) `(p1 : T -> proc _ T') p2,
  (forall x, atomic_equiv (p1 x) (p2 x)) ->
  atomic_equiv (Bind p p1) (Bind p p2).
Proof.
  unfold atomic_equiv; intros.
  split; intros.
  - invert H0.
    econstructor; eauto.
    eapply H; eauto.
  - invert H0.
    econstructor; eauto.
    eapply H; eauto.
Qed.

Theorem atomic_equiv_bind_bind' : forall `(p1 : proc Op T1) `(p2 : T1 -> proc _ T2) `(p3 : T1 -> T2 -> proc _ T3),
  atomic_equiv (Bind p1 (fun x => Bind (p2 x) (p3 x)))
               (Bind (Bind p1 (fun x => Bind (p2 x) (fun y => Ret (x, y))))
                     (fun p => p3 (fst p) (snd p))).
Proof.
  intros.
  rewrite atomic_equiv_bind_bind.
  eapply atomic_equiv_bind_a; intros.
  rewrite atomic_equiv_bind_bind.
  eapply atomic_equiv_bind_a; intros.
  rewrite atomic_equiv_ret_bind; simpl.
  reflexivity.
Qed.

Instance Atomic_proper_atomic_equiv :
  Proper (atomic_equiv ==> @exec_equiv_rx Op T) Atomic.
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

Instance Bind_proper_atomic_equiv :
  Proper (atomic_equiv ==>
          pointwise_relation T atomic_equiv ==>
          @atomic_equiv Op TR) Bind.
Proof.
  intros.
  intros p1a p1b H1.
  intros p2a p2b H2.
  split; intros; atomic_exec_inv.
  - apply H1 in H11.
    apply H2 in H12.
    eauto.
  - apply H1 in H11.
    apply H2 in H12.
    eauto.
Qed.


(** Trace inclusion for an entire threads_state *)

Definition trace_incl_ts_s {Op State} op_step (s s' : State) (ts1 ts2 : threads_state Op) :=
  forall tr,
    exec op_step s ts1 tr ->
    exec op_step s' ts2 tr.

Definition trace_incl_ts {Op State} op_step (ts1 ts2 : threads_state Op) :=
  forall (s : State),
    trace_incl_ts_s op_step s s ts1 ts2.

Instance trace_incl_ts_s_preorder :
  PreOrder (@trace_incl_ts_s Op State op_step s s).
Proof.
  constructor; repeat (hnf; intros).
  - eauto.
  - unfold trace_incl_ts_s in *; eauto 10.
Qed.

Instance trace_incl_ts_preorder :
  PreOrder (@trace_incl_ts Op State op_step).
Proof.
  constructor; hnf; intros.
  - hnf; reflexivity.
  - hnf; etransitivity; eauto.
Qed.

Instance exec_equiv_ts_to_trace_incl_ts :
  subrelation (@exec_equiv_ts Op) (@trace_incl_ts Op State op_step).
Proof.
  unfold subrelation; intros.
  unfold trace_incl_ts, trace_incl_ts_s; intros.
  apply H in H0.
  eauto.
Qed.

Theorem trace_incl_ts_s_trans : forall `(s0 : State) s1 s2 `(op_step : OpSemantics Op State) `(ts1 : threads_state Op) ts2 ts3,
  trace_incl_ts_s op_step s0 s1 ts1 ts2 ->
  trace_incl_ts_s op_step s1 s2 ts2 ts3 ->
  trace_incl_ts_s op_step s0 s2 ts1 ts3.
Proof.
  unfold trace_incl_ts_s; intros.
  apply H in H1.
  apply H0 in H1.
  intuition eauto.
Qed.

(** Trace inclusion for a single thread *)

Definition trace_incl_s `(s : State) tid `(op_step : OpSemantics Op State) `(p1 : proc Op T) (p2 : proc _ T) :=
  forall ts,
    trace_incl_ts_s op_step s s
      (ts [[ tid := Proc p1 ]])
      (ts [[ tid := Proc p2 ]]).

Definition trace_incl_opt {Op} `(op_step : OpSemantics Op State) p1 p2 :=
  forall (ts : threads_state Op) tid,
    trace_incl_ts op_step
      (ts [[ tid := p1 ]])
      (ts [[ tid := p2 ]]).

Definition trace_incl {Op T} `(op_step : OpSemantics Op State) (p1 p2 : proc Op T) :=
  trace_incl_opt op_step (Proc p1) (Proc p2).

(* natural definition of trace_incl_rx, defined in terms of all executions (that
is, without requiring counters be identical) *)
Definition trace_incl_rx' {Op T} `(op_step : OpSemantics Op State) (p1 p2 : proc Op T) :=
  forall TF (rx1 rx2: _ -> proc _ TF),
    (forall a, trace_incl op_step (rx1 a) (rx2 a)) ->
    trace_incl op_step (Bind p1 rx1) (Bind p2 rx2).

Definition trace_incl_ts_N n `(op_step: OpSemantics Op State) (ts1 ts2 : threads_state Op) :=
  forall tr s n',
    n' <= n ->
    exec_till op_step n' s ts1 tr ->
    exec op_step s ts2 tr.

Definition trace_incl_N n {Op T} `(op_step : OpSemantics Op State) (p1 p2 : proc Op T) :=
  forall (ts: threads_state Op) tid,
    trace_incl_ts_N n op_step
      (ts [[ tid := Proc p1 ]])
      (ts [[ tid := Proc p2 ]]).

Definition trace_incl_rx_N n {Op T} `(op_step: OpSemantics Op State) (p1 p2: proc Op T) :=
    forall TF (rx1 rx2 : _ -> proc _ TF) n0,
    n0 <= n ->
    (forall a, trace_incl_N (n0-1) op_step (rx1 a) (rx2 a)) ->
    trace_incl_N n0 op_step (Bind p1 rx1) (Bind p2 rx2).

Definition trace_incl_rx {Op T} `(op_step: OpSemantics Op State) (p1 p2: proc Op T) :=
  forall n, trace_incl_rx_N n op_step p1 p2.

Theorem trace_incl_rx'_all_n : forall `(op_step: OpSemantics Op State) T (p1 p2: proc Op T),
    (forall n, trace_incl_rx_N n op_step p1 p2) ->
    trace_incl_rx' op_step p1 p2.
Proof.
  unfold trace_incl_rx', trace_incl, trace_incl_opt, trace_incl_ts, trace_incl_ts_s,
  trace_incl_rx_N, trace_incl_N, trace_incl_ts_N.

  intros.
  apply exec_to_counter in H1; propositional.
  eapply H in H1; eauto.
  intros.
  eapply H0.
  eapply exec_till_to_exec; eauto.
Qed.

Theorem trace_incl_rx_all_n : forall `(op_step: OpSemantics Op State) T (p1 p2: proc Op T),
    (forall n, trace_incl_rx_N n op_step p1 p2) ->
    trace_incl_rx op_step p1 p2.
Proof.
  unfold trace_incl_rx; eauto.
Qed.

(* this is not true of trace_incl_rx' due to p1 and p2 possibly taking different
numbers of steps *)
Theorem trace_incl_rx_to_N : forall `(op_step: OpSemantics Op State) T (p1 p2: proc Op T),
    trace_incl_rx op_step p1 p2 ->
    forall n, trace_incl_rx_N n op_step p1 p2.
Proof.
  unfold trace_incl_rx; eauto.
Qed.

Theorem trace_incl_all_n : forall `(op_step: OpSemantics Op State) T (p1 p2: proc Op T),
    (forall n, trace_incl_N n op_step p1 p2) ->
    trace_incl op_step p1 p2.
Proof.
  unfold trace_incl_rx, trace_incl, trace_incl_opt, trace_incl_ts, trace_incl_ts_s,
  trace_incl_rx_N, trace_incl_N, trace_incl_ts_N.

  intros.
  apply exec_to_counter in H0; propositional.
  eauto.
Qed.

Theorem trace_incl_trace_incl_s : forall T `(op_step : OpSemantics Op State) (p1 p2 : proc Op T),
  trace_incl op_step p1 p2 <->
  (forall s tid,
    trace_incl_s s tid op_step p1 p2).
Proof.
  unfold trace_incl, trace_incl_opt, trace_incl_s, trace_incl_ts.
  split; eauto.
Qed.

Ltac RelInstance_t :=
  intros;
  let refl := try solve [ hnf; intros; reflexivity ] in
  let symm := try solve [ hnf; intros; try symmetry; eauto ] in
  let trans := try solve [ hnf; intros; etransitivity; eauto ] in
  match goal with
  | |- Reflexive _ =>
    hnf; intros; refl
  | |- PreOrder _ =>
    constructor; hnf; intros; [ refl | trans ]
  | |- Equivalence _ =>
    constructor; hnf; intros; [ refl | symm | trans ]
  end.

Notation RelInstance := (ltac:(RelInstance_t)) (only parsing).

Instance trace_incl_opt_preorder Op State (op_step: OpSemantics Op State) :
  PreOrder (trace_incl_opt op_step) := RelInstance.

Instance trace_incl_s_preorder :
  PreOrder (@trace_incl_s State s tid Op op_step T) := RelInstance.

Instance trace_incl_preorder :
  PreOrder (@trace_incl Op T State op_step) := RelInstance.

Instance exec_equiv_opt_to_trace_incl_opt :
  subrelation (@exec_equiv_opt Op) (@trace_incl_opt Op State op_step).
Proof.
  unfold subrelation; intros.
  unfold trace_incl_opt, trace_incl_ts, trace_incl_ts_s; intros.
  apply H in H0.
  eauto.
Qed.

Instance exec_equiv_to_trace_incl :
  subrelation (@exec_equiv Op T) (@trace_incl Op T State op_step).
Proof.
  unfold subrelation; intros.
  unfold trace_incl, trace_incl_opt, trace_incl_ts, trace_incl_ts_s; intros.
  apply H in H0.
  eauto.
Qed.

Instance trace_incl_proper :
  Proper (Basics.flip (@trace_incl Op T State op_step) ==>
          @trace_incl Op T State op_step ==>
          Basics.impl) (@trace_incl Op T State op_step).
Proof.
  intros.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  etransitivity; eauto.
  etransitivity; eauto.
Qed.

Instance trace_incl_proper_flip :
  Proper (@trace_incl Op T State op_step ==>
          Basics.flip (@trace_incl Op T State op_step) ==>
          Basics.flip Basics.impl) (@trace_incl Op T State op_step).
Proof.
  intros.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  repeat (etransitivity; eauto).
Qed.

Instance trace_incl_s_proper :
  Proper (Basics.flip (@trace_incl Op T State op_step) ==>
          @trace_incl Op T State op_step ==>
          Basics.impl) (@trace_incl_s State s tid Op op_step T).
Proof.
  intros.
  intros p1 p2 H12 p3 p4 H34 H; subst.
  unfold trace_incl_s, trace_incl_ts_s; intros.
  apply H12 in H0.
  apply H in H0.
  apply H34 in H0.
  eauto.
Qed.

Instance trace_incl_s_proper_flip :
  Proper (@trace_incl Op T State op_step ==>
          Basics.flip (@trace_incl Op T State op_step) ==>
          Basics.flip Basics.impl) (@trace_incl_s State s tid Op op_step T).
Proof.
  intros.
  intros p1 p2 H12 p3 p4 H34 H; subst.
  unfold trace_incl_s, trace_incl_ts_s; intros.
  apply H12 in H0.
  apply H in H0.
  apply H34 in H0.
  eauto.
Qed.

Instance trace_incl_s_exec_equiv_proper :
  Proper (exec_equiv ==> exec_equiv ==> iff)
         (@trace_incl_s State s tid Op op_step T).
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

Instance trace_incl_exec_equiv_proper :
  Proper (exec_equiv ==> exec_equiv ==> iff)
         (@trace_incl Op T State op_step).
Proof.
  unfold Proper, respectful, trace_incl, trace_incl_opt; intros.
  split; intros.
  rewrite <- H, <- H0; auto.
  rewrite H, H0; auto.
Qed.

Instance Proc_trace_incl_proper :
  Proper (@trace_incl Op T State op_step ==>
          @trace_incl_opt Op State op_step) (@Proc Op T).
Proof.
  intros.
  unfold exec_equiv.
  intros ts0 ts1 H; subst.
  eauto.
Qed.

Instance thread_upd_trace_incl_proper :
  Proper (eq ==> eq ==>
          @trace_incl_opt Op State op_step ==>
          trace_incl_ts op_step) (@thread_upd Op).
Proof.
  intros.
  intros ts0 ts1 H; subst.
  intros tid tid' H; subst.
  intros p1 p2 H.

  unfold trace_incl_opt in H.
  eauto.
Qed.

Lemma trace_incl_ts_s_proof_helper :
  forall `(p1 : proc Op T) (p2 : proc _ T) ts tid `(op_step : OpSemantics Op State) s,
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
  trace_incl_ts_s op_step s s
    (ts [[ tid := Proc p1 ]])
    (ts [[ tid := Proc p2 ]]).
Proof.
  unfold trace_incl_ts_s.
  intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
    remember (thread_upd ts tid p);
    generalize dependent ts;
    induction H; intros; subst; eauto; NoProc_upd
  end.

  cmp_ts tid tid0.
  + repeat maybe_proc_inv.
    eapply H; eauto.

  + ExecPrefix tid0 tid'.
    abstract_ts.
    eapply IHexec; intros; eauto with exec.
    eauto with exec.

    Grab Existential Variables.
    all: exact (Ret tt).
Qed.

Lemma trace_incl_proof_helper :
  forall `(p1 : proc Op T) p2 `(op_step : OpSemantics Op State),
  (forall tid tid' (ts: threads_state _) s s' result tr spawned evs,
    exec_tid op_step tid s p1 s' result spawned evs ->
    ts tid' = NoProc ->
    tid <> tid' ->
    exec op_step s' (ts [[tid' := spawned]] [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
      exec op_step s (ts [[tid := Proc p2]]) (prepend tid evs tr)) ->
  trace_incl op_step
    p1 p2.
Proof.
  unfold trace_incl, trace_incl_opt, trace_incl_ts.
  intros.

  eapply trace_incl_ts_s_proof_helper.
  eauto.
Qed.

Lemma trace_incl_s_proof_helper :
  forall `(p1 : proc Op T) p2 `(op_step : OpSemantics Op State) s tid,
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
  trace_incl_s s tid op_step
    p1 p2.
Proof.
  unfold trace_incl_s.
  intros.

  eapply trace_incl_ts_s_proof_helper.
  intros.
  eapply H in H2; eauto.
  propositional.
Qed.

Theorem trace_incl_op :
  forall `(p : T -> proc Op T') op `(op_step : OpSemantics Op State),
  trace_incl op_step
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
         `(op_step : OpSemantics Op State),
  trace_incl op_step
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

Theorem trace_incl_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2' `(op_step : OpSemantics Op State),
  (forall x, trace_incl op_step (p2 x) (p2' x)) ->
  trace_incl op_step (Bind p p2) (Bind p p2').
Proof.
  unfold trace_incl, trace_incl_opt,
         trace_incl_ts, trace_incl_ts_s.
  intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?pp) _ |- _ =>
    remember (thread_upd ts tid pp);
    generalize dependent ts;
    generalize dependent p;
    induction H; intros; subst; eauto; NoProc_upd

  end.

  cmp_ts tid0 tid.
  + autorewrite with t in *.
    repeat maybe_proc_inv.
    exec_tid_inv.
    destruct result0.

    * ExecPrefix tid tid'.
    * ExecPrefix tid tid'.

  + ExecPrefix tid0 tid'.
Qed.

Theorem trace_incl_s_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2' `(op_step : OpSemantics Op State) s tid,
  (forall s' x,
    exec_any op_step tid s p x s' ->
    trace_incl_s s' tid op_step (p2 x) (p2' x)) ->
  trace_incl_s s tid op_step (Bind p p2) (Bind p p2').
Proof.
  unfold trace_incl_s, trace_incl_ts_s.
  intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?pp) _ |- _ =>
    remember (thread_upd ts tid pp);
    generalize dependent ts;
    generalize dependent p;
    induction H; intros; subst; eauto; NoProc_upd
  end.

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

Theorem trace_incl_N_bind_a : forall `(p : proc Op T) `(p2 : T -> proc _ T') p2' `(op_step : OpSemantics Op State) n,
  (forall x, trace_incl_N (n-1) op_step (p2 x) (p2' x)) ->
  trace_incl_N n op_step (Bind p p2) (Bind p p2').
Proof.
  unfold trace_incl_N, trace_incl_ts_N.
  intros.

  match goal with
  | H : exec_till _ _ _ (thread_upd ?ts ?tid ?pp) _ |- _ =>
    remember (thread_upd ts tid pp);
    generalize dependent ts;
    generalize dependent p;
    induction H; intros; subst; eauto; NoProc_upd
  end.

  cmp_ts tid0 tid.
  + repeat maybe_proc_inv.
    exec_tid_inv.
    destruct result0.

    * epose_proof H.
      2: eassumption.
      omega.

      ExecPrefix tid tid'.

    * epose_proof IHexec_till.
      2: eauto.
      omega.

      ExecPrefix tid tid'.

  + ExecPrefix tid0 tid'.
    abstract_ts.
    eapply IHexec_till; eauto with exec.
    omega.
    auto with exec.
Qed.

Theorem trace_incl_N_le :
  forall `(op_step : OpSemantics Op State) T (p1 p2 : proc _ T) n1 n2,
    trace_incl_N n2 op_step p1 p2 ->
    n1 <= n2 ->
    trace_incl_N n1 op_step p1 p2.
Proof.
  repeat ( hnf; intros ).
  eapply H in H2; try omega.
  eauto.
Qed.

Instance trace_incl_ts_N_reflexive :
  Reflexive (@trace_incl_ts_N n Op State op_step) := RelInstance.
Proof.
  unfold trace_incl_ts_N; intros.
  eapply exec_till_to_exec; eauto.
Qed.

Instance trace_incl_N_reflexive :
  Reflexive (@trace_incl_N n Op T State op_step) := RelInstance.

Instance trace_incl_rx_preorder :
  PreOrder (@trace_incl_rx Op T State op_step).
Proof.
  unfold trace_incl_rx.
  RelInstance_t.
  - unfold trace_incl_rx_N; intros.
    eapply trace_incl_N_bind_a.
    eauto.
  - repeat (hnf; intros).
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

Instance Bind_trace_incl_proper_2 :
  Proper (eq ==>
          pointwise_relation T0 (@trace_incl Op T State op_step) ==>
          @trace_incl Op T State op_step) Bind.
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
         `(op_step : OpSemantics Op State),
  trace_incl op_step
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
  rewrite app_nil_r; auto.
Qed.

Lemma trace_incl_atomic :
  forall `(p1 : proc Op T)
         `(p2 : T -> proc Op T2)
         `(op_step : OpSemantics Op State),
  trace_incl op_step
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
    rewrite exec_equiv_norx_bind_bind.
    eauto.
  - ExecPrefix tid tid'.
  - abstract_tr.
    ExecPrefix tid tid'.
    rewrite thread_upd_same_eq with (tid:=tid') in * by auto;
      eauto with nocore exec.
    reflexivity.
Qed.

Theorem trace_incl_rx_to_exec :
  forall `(op_step: OpSemantics Op State) T (p1 p2: proc _ T)
    (ts: threads_state _) s tid tr,
    trace_incl_rx op_step p1 p2 ->
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
  : forall (Op : Type -> Type)
      T (p1 p2 : proc Op T) (State : Type)
      (op_step : OpSemantics Op State),
    trace_incl_rx op_step p1 p2 ->
    trace_incl_rx op_step (Spawn p1) (Spawn p2).
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
  forall `(op_step : OpSemantics Op State) T (p1 p2 : proc Op T),
    trace_incl_rx op_step p1 p2 ->
    forall `(rx : _ -> proc _ TF),
      trace_incl op_step (Bind p1 rx) (Bind p2 rx).
Proof.
  repeat (hnf; intros).
  eapply exec_to_counter in H0; propositional.
  eapply H; eauto.
  reflexivity.
Qed.

Theorem trace_incl_to_trace_incl_rx :
  forall `(op_step : OpSemantics Op State) T (p1 p2 : proc Op T),
    (forall `(rx : _ -> proc _ TF),
      trace_incl op_step (Bind p1 rx) (Bind p2 rx)) ->
    trace_incl_rx op_step p1 p2.
Proof.
  repeat (hnf; intros).
  assert (trace_incl_rx op_step p1 p1) by reflexivity.
  eapply H4 in H3; [ | reflexivity | eassumption | omega ].
  eapply H; eauto.
Qed.

Theorem trace_incl_N_ret_bind :
  forall `(op_step : OpSemantics Op State) `(v : T) TF (rx1 rx2 : _ -> proc _ TF) n,
    (forall a, trace_incl_N (n - 1) op_step (rx1 a) (rx2 a)) ->
    trace_incl_N n op_step (Bind (Ret v) rx1) (Bind (Ret v) rx2).
Proof.
  repeat ( intro; intros ).
  match goal with
  | H : exec_till _ _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
    remember (thread_upd ts tid (Proc p));
    generalize dependent ts;
    induction H; intros; subst; eauto; NoProc_upd
  end.

  cmp_ts tid0 tid.
  * repeat maybe_proc_inv.
    repeat exec_tid_inv.
    replace (S n - 1) with n in * by omega.
    eapply H in H4; try omega.
    ExecPrefix tid tid'.

  * ExecPrefix tid0 tid'.
    abstract_ts.
    eapply IHexec_till; eauto with exec.
    omega.
    eauto with exec.
Qed.

Theorem trace_incl_rx_N_le :
  forall `(op_step : OpSemantics Op State) T (p1 p2 : proc _ T) n1 n2,
    trace_incl_rx_N n2 op_step p1 p2 ->
    n1 <= n2 ->
    trace_incl_rx_N n1 op_step p1 p2.
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
  forall T Op (p1 p2 : option T -> proc Op T)
         `(op_step : OpSemantics Op State)
         (c : T -> bool) n v,
    (forall v', trace_incl_rx_N (n-1) op_step (p1 v') (p2 v')) ->
    trace_incl_rx_N n op_step (Until c p1 v) (Until c p2 v).
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
        H' : forall _, trace_incl_rx_N _ _ _ _ |- _ =>
        eapply H' in H; try omega
      end.

      ExecPrefix tid tid'.
      unfold until1.
      rewrite exec_equiv_bind_bind.
      eassumption.
      instantiate (1 := n1); omega.

      simpl; intros.
      destruct (Bool.bool_dec (c a)).
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
      rewrite thread_upd_abc_to_cab in * by auto.
      eapply IHn with (n0:=n1) (n':=n1) (rx1:=rx1); intros; try omega; eauto.
      eapply trace_incl_rx_N_le; eauto; omega.
      eapply trace_incl_N_le; eauto; omega.
Qed.

Theorem trace_incl_rx_until' :
  forall T Op (p1 p2 : option T -> proc Op T)
         `(op_step : OpSemantics Op State)
         (c : T -> bool) v,
    (forall n v', trace_incl_rx_N n op_step (p1 v') (p2 v')) ->
    forall n, trace_incl_rx_N n op_step (Until c p1 v) (Until c p2 v).
Proof.
  repeat ( intro; intros ).
  eapply trace_incl_rx_until_helper in H3.
  5: reflexivity.
  eassumption.
  intros. eapply H.
  reflexivity.
  intros; eapply trace_incl_N_le; eauto; omega.
Qed.

Theorem trace_incl_rx_until :
  forall T Op (p1 p2 : option T -> proc Op T)
    `(op_step : OpSemantics Op State)
    (c : T -> bool) v,
    (forall v', trace_incl_rx op_step (p1 v') (p2 v')) ->
    trace_incl_rx op_step (Until c p1 v) (Until c p2 v).
Proof.
  repeat ( intro; intros ).
  eapply trace_incl_rx_until_helper in H3.
  5: reflexivity.
  eassumption.
  intros. eapply H.
  reflexivity.
  intros; eapply trace_incl_N_le; eauto; omega.
Qed.

(** Correspondence between different layers *)

Definition traces_match_ts {opLoT opMidT State} lo_step hi_step
                           (ts1 : threads_state opLoT)
                           (ts2 : threads_state opMidT) :=
  forall (s : State) tr1,
    exec lo_step s ts1 tr1 ->
      exec hi_step s ts2 tr1.

Instance traces_match_ts_proper :
  Proper (@trace_incl_ts opLoT State lo_step ==>
          exec_equiv_ts ==>
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
