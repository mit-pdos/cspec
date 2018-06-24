Require Import ConcurProc.
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import Helpers.FinMap.
Require Import List.
Require Import Omega.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


(** A strong notion of execution equivalence, independent of semantics *)

Definition exec_equiv_ts {opT} (ts1 ts2 : @threads_state opT) :=
  forall State op_step (s : State) tr,
    exec_prefix op_step s ts1 tr <->
    exec_prefix op_step s ts2 tr.

Definition exec_equiv_opt `(p1 : maybe_proc opT) p2 :=
  forall (ts : threads_state) tid,
    exec_equiv_ts (ts [[ tid := p1 ]]) (ts [[ tid := p2 ]]).

Definition exec_equiv `(p1 : proc opT T) (p2 : proc _ T) :=
  exec_equiv_opt (Proc p1) (Proc p2).

Definition exec_equiv_rx `(p1 : proc opT T) (p2 : proc _ T) :=
  forall TR (rx : T -> proc _ TR),
    exec_equiv (Bind p1 rx) (Bind p2 rx).

Instance exec_equiv_ts_equivalence :
  Equivalence (@exec_equiv_ts opT).
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
  Equivalence (@exec_equiv_opt opT).
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
  Equivalence (@exec_equiv opT T).
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
  Equivalence (@exec_equiv_rx opT T).
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
  Proper (eq ==> eq ==> exec_equiv_opt ==> exec_equiv_ts) (@thread_upd opT).
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
  Proper (exec_equiv ==> exec_equiv_opt) (@Proc opT T).
Proof.
  intros.
  unfold exec_equiv.
  intros ts0 ts1 H; subst.
  eauto.
Qed.

Theorem exec_equiv_ret_None : forall opT `(v : T),
  @exec_equiv_opt opT (Proc (Ret v)) NoProc.
Proof.
  split; intros;
    unfold exec_prefix in *; repeat deex.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      repeat exec_tid_inv.
      simpl. eauto.

    * rewrite thread_upd_ne_comm in * by eauto.
      edestruct IHexec. eauto.

      eexists.
      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eauto.

  - replace tr with (prepend tid nil tr) by reflexivity.
    eexists.
    eapply ExecOne with (tid := tid).
      rewrite thread_upd_eq. eauto.
      eauto.
    autorewrite with t.
    eauto.
Qed.

Theorem exec_equiv_bind_ret : forall `(p : proc opT T),
  exec_equiv (Bind p Ret) p.
Proof.
  unfold exec_equiv; split; intros;
    unfold exec_prefix in *; repeat deex.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.

      destruct result0.
      {
        edestruct exec_equiv_ret_None.
        edestruct H.
        unfold exec_prefix; eauto.

        eexists.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq in * by auto. eauto.
          eauto.
        autorewrite with t.
        eauto.
      }

      {
        edestruct IHexec. eauto.

        eexists.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq in * by auto. eauto.
          eauto.
        autorewrite with t.
        eauto.
      }

    * rewrite thread_upd_ne_comm in * by eauto.
      edestruct IHexec; eauto.
      eexists.
      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eauto.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.

      destruct result.
      {
        edestruct exec_equiv_ret_None.
        edestruct H2.
        unfold exec_prefix; eauto.

        eexists.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t in *.
        eauto.
      }

      {
        edestruct IHexec; eauto.
        eexists.
        eapply ExecOne with (tid := tid).
          rewrite thread_upd_eq. eauto.
          eauto.
        autorewrite with t in *.
        eauto.
      }

    * rewrite thread_upd_ne_comm in * by eauto.
      edestruct IHexec; eauto.
      eexists.
      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eauto.
Qed.

Instance exec_equiv_rx_to_exec_equiv :
  subrelation (@exec_equiv_rx opT T) exec_equiv.
Proof.
  unfold subrelation, exec_equiv_rx; intros.
  rewrite <- exec_equiv_bind_ret with (p := x).
  rewrite <- exec_equiv_bind_ret with (p := y).
  eauto.
Qed.

Theorem exec_equiv_rx_proof_helper : forall `(p1 : proc opT T) p2,
  (forall tid `(s : State) s' op_step ts tr evs `(rx : _ -> proc _ TR) result,
    exec_tid op_step tid s (Bind p1 rx) s' result evs ->
    exec_prefix op_step s' (ts [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
    exec_prefix op_step s (ts [[tid := Proc (Bind p2 rx)]]) (prepend tid evs tr)) ->
  (forall tid `(s : State) s' op_step ts tr evs `(rx : _ -> proc _ TR) result,
    exec_tid op_step tid s (Bind p2 rx) s' result evs ->
    exec_prefix op_step s' (ts [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
    exec_prefix op_step s (ts [[tid := Proc (Bind p1 rx)]]) (prepend tid evs tr)) ->
  exec_equiv_rx p1 p2.
Proof.
  split; intros.
  - match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      unfold exec_prefix in H; repeat deex;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst; autorewrite with t in *.
    * repeat maybe_proc_inv. eauto.
    * eapply ExecPrefixOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_ne_comm by eauto.
      eapply IHexec.
      rewrite thread_upd_ne_comm; eauto.

  - match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      unfold exec_prefix in H; repeat deex;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst; autorewrite with t in *.
    * repeat maybe_proc_inv. eauto.
    * eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eauto.
        rewrite thread_upd_ne_comm by eauto.
      eapply IHexec.
      rewrite thread_upd_ne_comm; auto.
Qed.

Theorem exec_equiv_ret_bind : forall `(v : T) `(p : T -> proc opT T'),
  exec_equiv_rx (Bind (Ret v) p) (p v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv; eauto.
  - rewrite <- app_nil_l with (l := evs).
    rewrite prepend_app.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t.
    eauto.
Qed.

Theorem exec_equiv_atomicret_bind : forall `(v : T) `(p : T -> proc opT T'),
  exec_equiv_rx (Bind (Atomic (Ret v)) p) (p v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv.
    repeat atomic_exec_inv.
    eauto.
  - rewrite <- app_nil_l with (l := evs).
    rewrite prepend_app.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t.
    eauto.
Qed.

Theorem exec_equiv_atomicret_ret : forall opT `(v : T),
  @exec_equiv_rx opT _ (Atomic (Ret v)) (Ret v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv.
    repeat atomic_exec_inv.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t; eauto.
  - repeat exec_tid_inv.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t; eauto.
Qed.

Theorem exec_equiv_bind_bind : forall `(p1 : proc opT T1) `(p2 : T1 -> proc opT T2) `(p3 : T2 -> proc opT T3),
  exec_equiv_rx (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      unfold exec_prefix in H; repeat deex;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.
      exec_tid_inv.
      eapply ExecPrefixOne with (tid := tid).
        rewrite thread_upd_eq. eauto.
        eauto.
      autorewrite with t.

      destruct result0; eauto.

    * eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eapply IHexec.
      rewrite thread_upd_ne_comm; eauto.

  - match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid (Proc ?p)) _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      unfold exec_prefix in H; repeat deex;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.

      eapply ExecPrefixOne with (tid := tid).
        rewrite thread_upd_eq. eauto.
        eauto.
      autorewrite with t.

      destruct result; eauto.

    * rewrite thread_upd_ne_comm in * by eauto.
      eapply ExecPrefixOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eauto.
Qed.

Theorem exec_equiv_norx_bind_bind : forall `(p1 : proc opT T1) `(p2 : T1 -> proc opT T2) `(p3 : T2 -> proc opT T3),
  exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  intros.
  rewrite exec_equiv_bind_bind.
  reflexivity.
Qed.

Theorem exec_equiv_bind_a : forall `(p : proc opT T) `(p1 : T -> proc _ T') p2,
  (forall x, exec_equiv (p1 x) (p2 x)) ->
  exec_equiv (Bind p p1) (Bind p p2).
Proof.
  unfold exec_equiv; split; intros.
  - match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      unfold exec_prefix in H; repeat deex;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      eapply ExecPrefixOne with (tid := tid).
        rewrite thread_upd_eq. eauto.
        eauto.
      autorewrite with t.

      destruct result0; eauto.
      eapply H. eauto.

    * eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eapply IHexec.
      rewrite thread_upd_ne_comm; eauto.

  - match goal with
    | H : exec_prefix _ _ (thread_upd ?ts ?tid (Proc ?pp)) _ |- _ =>
      remember (thread_upd ts tid (Proc pp));
      generalize dependent ts;
      generalize dependent p;
      unfold exec_prefix in H; repeat deex;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      eapply ExecPrefixOne with (tid := tid).
        rewrite thread_upd_eq. eauto.
        eauto.
      autorewrite with t.

      destruct result0; eauto.
      eapply H. eauto.

    * eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eapply IHexec.
      rewrite thread_upd_ne_comm; eauto.
Qed.

Theorem exec_equiv_bind_bind' : forall `(p1 : proc opT T1) `(p2 : T1 -> proc _ T2) `(p3 : T1 -> T2 -> proc _ T3),
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

Theorem exec_equiv_until : forall `(p : option T -> proc opT T) (c : T -> bool) v,
  exec_equiv_rx (Until c p v) (until1 c p v).
Proof.
  intros.
  eapply exec_equiv_rx_proof_helper; intros.
  - repeat exec_tid_inv.
    simpl; eauto.
  - rewrite <- app_nil_l with (l := evs).
    rewrite prepend_app.
    eapply ExecPrefixOne.
      autorewrite with t; eauto.
      eauto.
      autorewrite with t.
    eapply ExecPrefixOne.
      autorewrite with t; eauto.
      eauto.
      autorewrite with t.
    eauto.
Qed.

Theorem exec_equiv_until_once : forall opT `(p : proc opT T),
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
          @exec_equiv_rx opT TR) Bind.
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

Theorem exec_equiv_ts_upd_same : forall `(ts : @threads_state opT) p tid,
  ts [[ tid ]] = p ->
  exec_equiv_ts ts (ts [[ tid := p ]]).
Proof.
  intros.
  autorewrite with t; reflexivity.
Qed.

Instance exec_prefix_proper_exec_equiv :
  Proper (eq ==> eq ==> exec_equiv_ts ==> eq ==> iff) (@exec_prefix opT State).
Proof.
  intros.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  intros ? ? ?; subst.
  apply H.
Qed.

Theorem exec_equiv_rx_bind_ret : forall `(p : proc opT T),
  exec_equiv_rx (Bind p Ret) p.
Proof.
  unfold exec_equiv_rx; intros.
  rewrite exec_equiv_bind_bind.
  eapply exec_equiv_bind_a; intros.
  rewrite exec_equiv_ret_bind.
  reflexivity.
Qed.



(** A version of [exec_equiv] for [exec] instead of [exec_prefix]. *)

Definition exec_equiv_ts_N (n1 n2 : nat) {opT} (ts1 ts2 : @threads_state opT) :=
  forall State op_step (s : State) tr,
    exec op_step s ts1 tr n1 <->
    exec op_step s ts2 tr n2.

Definition exec_equiv_opt_N n1 n2 `(p1 : maybe_proc opT) p2 :=
  forall (ts : threads_state) tid,
    exec_equiv_ts_N n1 n2 (ts [[ tid := p1 ]]) (ts [[ tid := p2 ]]).

Definition exec_equiv_N n1 n2 `(p1 : proc opT T) (p2 : proc _ T) :=
  exec_equiv_opt_N n1 n2 (Proc p1) (Proc p2).

Definition exec_equiv_rx_N n1 n2 `(p1 : proc opT T) (p2 : proc _ T) :=
  forall TR (rx : T -> proc _ TR),
    exec_equiv_N n1 n2 (Bind p1 rx) (Bind p2 rx).

Instance exec_equiv_ts_N_equivalence :
  Equivalence (@exec_equiv_ts_N n n opT).
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

Instance exec_equiv_opt_N_equivalence :
  Equivalence (@exec_equiv_opt_N n n opT).
Proof.
  split.
  - unfold exec_equiv_opt_N, Reflexive; intros.
    reflexivity.
  - unfold exec_equiv_opt_N, Symmetric; intros.
    symmetry. eauto.
  - intros t1 t2 t3.
    unfold exec_equiv; split; intros.
    + eapply H in H1; eauto.
      eapply H0 in H1.
      eauto.
    + eapply H; eauto.
      eapply H0; eauto.
Qed.

Instance exec_equiv_N_equivalence :
  Equivalence (@exec_equiv_N n n opT T).
Proof.
  unfold exec_equiv_N.
  split.
  - intro t.
    reflexivity.
  - unfold Symmetric, exec_equiv_opt; intros.
    symmetry. eauto.
  - unfold Transitive; intros.
    etransitivity; eauto.
Qed.

Instance exec_equiv_rx_N_equivalence :
  Equivalence (@exec_equiv_rx_N n n opT T).
Proof.
  unfold exec_equiv_rx_N.
  split.
  - intro t.
    reflexivity.
  - unfold Symmetric, exec_equiv_opt_N; intros.
    symmetry. eauto.
  - unfold Transitive; intros.
    etransitivity; eauto.
Qed.

Theorem exec_equiv_N_bind_bind : forall `(p1 : proc opT T1) `(p2 : T1 -> proc opT T2) `(p3 : T2 -> proc opT T3) n,
  exec_equiv_N n n (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.
      eapply ExecOne with (tid := tid).
        rewrite thread_upd_eq. eauto.
        eauto.
      autorewrite with t.

      destruct result; eauto.

    * eapply ExecOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eapply IHexec.
      rewrite thread_upd_ne_comm; eauto.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.

      eapply ExecOne with (tid := tid).
        rewrite thread_upd_eq. eauto.
        eauto.
      autorewrite with t.

      destruct result0; eauto.

    * rewrite thread_upd_ne_comm in * by eauto.
      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eauto.
Qed.

Theorem exec_equiv_rx_N_bind_bind : forall `(p1 : proc opT T1) `(p2 : T1 -> proc opT T2) `(p3 : T2 -> proc opT T3) n,
  exec_equiv_rx_N n n (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  split; intros.
  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.
      exec_tid_inv.
      eapply ExecOne with (tid := tid).
        rewrite thread_upd_eq. eauto.
        eauto.
      autorewrite with t.

      destruct result0; eauto.

    * eapply ExecOne with (tid := tid0).
        autorewrite with t in *; eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eapply IHexec.
      rewrite thread_upd_ne_comm; eauto.

  - match goal with
    | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ _ |- _ =>
      remember (thread_upd ts tid (Proc p));
      generalize dependent ts;
      generalize dependent p1;
      induction H; intros; subst; eauto
    end.

    destruct (tid0 == tid); subst.
    * autorewrite with t in *.
      repeat maybe_proc_inv.
      exec_tid_inv.
      exec_tid_inv.

      eapply ExecOne with (tid := tid).
        rewrite thread_upd_eq. eauto.
        eauto.
      autorewrite with t.

      destruct result; eauto.

    * rewrite thread_upd_ne_comm in * by eauto.
      eapply ExecOne with (tid := tid0).
        rewrite thread_upd_ne in * by auto. eauto.
        eauto.
      rewrite thread_upd_ne_comm by auto.
      eauto.
Qed.


(** A strong notion of equivalence for programs inside atomic sections.
    Basically the same as above, but defined as an underlying [atomic_exec]
    rather than [exec]. *)

Definition atomic_equiv `(p1 : proc opT T) p2 :=
  forall State op_step (s s' : State) r tid evs,
    atomic_exec op_step p1 tid s r s' evs <->
    atomic_exec op_step p2 tid s r s' evs.

Instance atomic_equiv_equivalence :
  Equivalence (@atomic_equiv opT T).
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
  Proper (atomic_equiv ==> atomic_equiv ==> iff) (@atomic_equiv opT T).
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

Theorem atomic_equiv_ret_bind : forall `(v : T) `(p : T -> proc opT T'),
  atomic_equiv (Bind (Ret v) p) (p v).
Proof.
  split; intros.
  - atomic_exec_inv.
    inversion H9; clear H9; subst; repeat sigT_eq.
    eauto.
  - rewrite <- app_nil_l.
    eauto.
Qed.

Theorem atomic_equiv_bind_ret : forall `(p : proc opT T),
  atomic_equiv (Bind p Ret) p.
Proof.
  split; intros.
  - atomic_exec_inv.
    inversion H10; clear H10; subst; repeat sigT_eq.
    rewrite app_nil_r.
    eauto.
  - rewrite <- app_nil_r.
    eauto.
Qed.

Theorem atomic_equiv_bind_bind : forall `(p1 : proc opT T1) `(p2 : T1 -> proc opT T2) `(p3 : T2 -> proc opT T3),
  atomic_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  split; intros.
  - atomic_exec_inv.
    inversion H9; clear H9; subst; repeat sigT_eq.
    rewrite <- app_assoc.
    eauto.
  - atomic_exec_inv.
    inversion H10; clear H10; subst; repeat sigT_eq.
    rewrite app_assoc.
    eauto.
Qed.

Theorem atomic_equiv_bind_a : forall `(p : proc opT T) `(p1 : T -> proc _ T') p2,
  (forall x, atomic_equiv (p1 x) (p2 x)) ->
  atomic_equiv (Bind p p1) (Bind p p2).
Proof.
  unfold atomic_equiv; intros.
  split; intros.
  - inversion H0; clear H0; repeat sigT_eq.
    econstructor; eauto.
    eapply H; eauto.
  - inversion H0; clear H0; repeat sigT_eq.
    econstructor; eauto.
    eapply H; eauto.
Qed.

Theorem atomic_equiv_bind_bind' : forall `(p1 : proc opT T1) `(p2 : T1 -> proc _ T2) `(p3 : T1 -> T2 -> proc _ T3),
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
  Proper (atomic_equiv ==> @exec_equiv_rx opT T) Atomic.
Proof.
  intros.
  intros p1 p2 H.
  eapply exec_equiv_rx_proof_helper; intros;
    repeat exec_tid_inv.
  - apply H in H7.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t. eauto.
  - apply H in H7.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t. eauto.
Qed.

Instance Bind_proper_atomic_equiv :
  Proper (atomic_equiv ==>
          pointwise_relation T atomic_equiv ==>
          @atomic_equiv opT TR) Bind.
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

Definition trace_incl_ts_s {opT State} op_step (s s' : State) (ts1 ts2 : @threads_state opT) :=
  forall tr,
    exec_prefix op_step s ts1 tr ->
     exec_prefix op_step s' ts2 tr.

Definition trace_incl_ts {opT State} op_step (ts1 ts2 : @threads_state opT) :=
  forall (s : State),
    trace_incl_ts_s op_step s s ts1 ts2.

Definition trace_incl_ts_s_N n {opT State} op_step (s s' : State) (ts1 ts2 : @threads_state opT) :=
  forall tr n',
    n' <= n ->
    exec op_step s ts1 tr n' ->
    exec_prefix op_step s' ts2 tr.

Definition trace_incl_ts_N n {opT State} op_step (ts1 ts2 : @threads_state opT) :=
  forall (s : State),
    trace_incl_ts_s_N n op_step s s ts1 ts2.

Instance trace_incl_ts_s_preorder :
  PreOrder (@trace_incl_ts_s opT State op_step s s).
Proof.
  constructor; repeat (hnf; intros).
  - unfold exec_prefix in *; propositional; eauto.
  - unfold trace_incl_ts_s, exec_prefix in *; eauto 10.
Qed.

Instance trace_incl_ts_preorder :
  PreOrder (@trace_incl_ts opT State op_step).
Proof.
  constructor; hnf; intros.
  - hnf; reflexivity.
  - hnf; etransitivity; eauto.
Qed.

Instance exec_equiv_ts_to_trace_incl_ts :
  subrelation (@exec_equiv_ts opT) (@trace_incl_ts opT State op_step).
Proof.
  unfold subrelation; intros.
  unfold trace_incl_ts, trace_incl_ts_s; intros.
  apply H in H0.
  eauto.
Qed.

Theorem trace_incl_ts_s_trans : forall `(s0 : State) s1 s2 `(op_step : OpSemantics opT State) `(ts1 : @threads_state opT) ts2 ts3,
  trace_incl_ts_s op_step s0 s1 ts1 ts2 ->
  trace_incl_ts_s op_step s1 s2 ts2 ts3 ->
  trace_incl_ts_s op_step s0 s2 ts1 ts3.
Proof.
  unfold trace_incl_ts_s; intros.
  apply H in H1.
  apply H0 in H1.
  intuition eauto.
Qed.

Instance trace_incl_ts_s_N_refl :
  Reflexive (@trace_incl_ts_s_N n opT State op_step s s).
Proof.
  unfold Reflexive.
  unfold trace_incl_ts_s_N; intros.
  eauto.
Qed.

Instance trace_incl_ts_N_refl :
  Reflexive (@trace_incl_ts_N n opT State op_step).
Proof.
  unfold Reflexive, trace_incl_ts_N; intros.
  reflexivity.
Qed.


(** Trace inclusion for a single thread *)

Definition trace_incl_s `(s : State) tid `(op_step : OpSemantics opT State) `(p1 : proc opT T) (p2 : proc _ T) :=
  forall ts,
    trace_incl_ts_s op_step s s
      (ts [[ tid := Proc p1 ]])
      (ts [[ tid := Proc p2 ]]).

Definition trace_incl_opt {opT} `(op_step : OpSemantics opT State) p1 p2 :=
  forall (ts : @threads_state opT) tid,
    trace_incl_ts op_step
      (ts [[ tid := p1 ]])
      (ts [[ tid := p2 ]]).

Definition trace_incl {opT T} `(op_step : OpSemantics opT State) (p1 p2 : proc opT T) :=
  trace_incl_opt op_step (Proc p1) (Proc p2).


Definition trace_incl_s_N n `(s : State) tid `(op_step : OpSemantics opT State) `(p1 : proc opT T) (p2 : proc _ T) :=
  forall ts,
    trace_incl_ts_s_N n op_step s s
      (ts [[ tid := Proc p1 ]])
      (ts [[ tid := Proc p2 ]]).

Definition trace_incl_opt_N n {opT} `(op_step : OpSemantics opT State) p1 p2 :=
  forall (ts : @threads_state opT) tid,
    trace_incl_ts_N n op_step
      (ts [[ tid := p1 ]])
      (ts [[ tid := p2 ]]).

Definition trace_incl_N n {opT T} `(op_step : OpSemantics opT State) (p1 p2 : proc opT T) :=
  trace_incl_opt_N n op_step (Proc p1) (Proc p2).


Definition trace_incl_rx_N n {opT T} `(op_step : OpSemantics opT State) (p1 p2 : proc opT T) :=
  forall TF (rx1 rx2 : _ -> proc _ TF) n0,
    n0 <= n ->
    (forall a, trace_incl_N (n0-1) op_step (rx1 a) (rx2 a)) ->
    trace_incl_N n0 op_step (Bind p1 rx1) (Bind p2 rx2).

Definition trace_incl_rx {opT T} `(op_step : OpSemantics opT State) (p1 p2 : proc opT T) :=
  forall n,
    trace_incl_rx_N n op_step p1 p2.


Theorem trace_incl_trace_incl_s : forall T `(op_step : OpSemantics opT State) (p1 p2 : proc opT T),
  trace_incl op_step p1 p2 <->
  (forall s tid,
    trace_incl_s s tid op_step p1 p2).
Proof.
  unfold trace_incl, trace_incl_opt, trace_incl_s, trace_incl_ts.
  split; eauto.
Qed.


Instance trace_incl_opt_preorder :
  PreOrder (@trace_incl_opt opT State op_step).
Proof.
  split.
  - unfold Reflexive; intros.
    unfold trace_incl_opt; intros.
    reflexivity.
  - unfold Transitive; intros.
    unfold trace_incl_opt; intros.
    etransitivity; eauto.
Qed.

Instance trace_incl_s_preorder :
  PreOrder (@trace_incl_s State s tid opT op_step T).
Proof.
  split.
  - unfold Reflexive; intros.
    unfold trace_incl_s; intros.
    reflexivity.
  - unfold Transitive; intros.
    unfold trace_incl_s; intros.
    etransitivity; eauto.
Qed.

Instance trace_incl_preorder :
  PreOrder (@trace_incl opT T State op_step).
Proof.
  split.
  - unfold Reflexive; intros.
    unfold trace_incl; intros.
    reflexivity.
  - unfold Transitive; intros.
    unfold trace_incl; intros.
    etransitivity; eauto.
Qed.

Instance exec_equiv_opt_to_trace_incl_opt :
  subrelation (@exec_equiv_opt opT) (@trace_incl_opt opT State op_step).
Proof.
  unfold subrelation; intros.
  unfold trace_incl_opt, trace_incl_ts, trace_incl_ts_s; intros.
  apply H in H0.
  eauto.
Qed.

Instance exec_equiv_to_trace_incl :
  subrelation (@exec_equiv opT T) (@trace_incl opT T State op_step).
Proof.
  unfold subrelation; intros.
  unfold trace_incl, trace_incl_opt, trace_incl_ts, trace_incl_ts_s; intros.
  apply H in H0.
  eauto.
Qed.

Instance trace_incl_proper :
  Proper (Basics.flip (@trace_incl opT T State op_step) ==>
          @trace_incl opT T State op_step ==>
          Basics.impl) (@trace_incl opT T State op_step).
Proof.
  intros.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  repeat (etransitivity; eauto).
Qed.

Instance trace_incl_proper_flip :
  Proper (@trace_incl opT T State op_step ==>
          Basics.flip (@trace_incl opT T State op_step) ==>
          Basics.flip Basics.impl) (@trace_incl opT T State op_step).
Proof.
  intros.
  intros p1 p2 H21 p3 p4 H34 H; subst.
  unfold Basics.flip in *.
  repeat (etransitivity; eauto).
Qed.

Instance trace_incl_s_proper :
  Proper (Basics.flip (@trace_incl opT T State op_step) ==>
          @trace_incl opT T State op_step ==>
          Basics.impl) (@trace_incl_s State s tid opT op_step T).
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
  Proper (@trace_incl opT T State op_step ==>
          Basics.flip (@trace_incl opT T State op_step) ==>
          Basics.flip Basics.impl) (@trace_incl_s State s tid opT op_step T).
Proof.
  intros.
  intros p1 p2 H12 p3 p4 H34 H; subst.
  unfold trace_incl_s, trace_incl_ts_s; intros.
  apply H12 in H0.
  apply H in H0.
  apply H34 in H0.
  eauto.
Qed.

Instance trace_incl_exec_equiv_proper :
  Proper (exec_equiv ==> exec_equiv ==> iff)
         (@trace_incl opT T State op_step).
Proof.
  intros p1 p1' ?.
  intros p2 p2' ?.
  split; intros.
  - unfold trace_incl, trace_incl_opt,
           trace_incl_ts, trace_incl_ts_s; intros.
    apply H in H2.
    apply H1 in H2.
    apply H0 in H2.
    eauto.
  - unfold trace_incl, trace_incl_opt,
           trace_incl_ts, trace_incl_ts_s; intros.
    apply H in H2.
    apply H1 in H2.
    apply H0 in H2.
    eauto.
Qed.

Instance trace_incl_s_exec_equiv_proper :
  Proper (exec_equiv ==> exec_equiv ==> iff)
         (@trace_incl_s State s tid opT op_step T).
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

Instance Proc_trace_incl_proper :
  Proper (@trace_incl opT T State op_step ==>
          @trace_incl_opt opT State op_step) (@Proc opT T).
Proof.
  intros.
  unfold exec_equiv.
  intros ts0 ts1 H; subst.
  eauto.
Qed.

Instance thread_upd_trace_incl_proper :
  Proper (eq ==> eq ==>
          @trace_incl_opt opT State op_step ==>
          trace_incl_ts op_step) (@thread_upd opT).
Proof.
  intros.
  intros ts0 ts1 H; subst.
  intros tid tid' H; subst.
  intros p1 p2 H.

  unfold trace_incl_opt in H.
  eauto.
Qed.

Lemma trace_incl_ts_s_proof_helper :
  forall `(p1 : proc opT T) (p2 : proc _ T) ts tid `(op_step : OpSemantics opT State) s,
  (forall ts s0 s' result tr evs,
    exec_others op_step tid s s0 ->
    exec_tid op_step tid s0 p1 s' result evs ->
    exec_prefix op_step s' (ts [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
      exec_prefix op_step s0 ts [[tid := Proc p2]] (prepend tid evs tr)) ->
  trace_incl_ts_s op_step s s
    (ts [[ tid := Proc p1 ]])
    (ts [[ tid := Proc p2 ]]).
Proof.
  unfold trace_incl_ts_s.
  intros.

  match goal with
  | H : exec_prefix _ _ (thread_upd ?ts ?tid ?p) _ |- _ =>
    remember (thread_upd ts tid p);
    generalize dependent ts;
    unfold exec_prefix in H; repeat deex;
    induction H; intros; subst; eauto
  end.

  destruct (tid == tid0); subst.
  + autorewrite with t in *.
    repeat maybe_proc_inv.
    eapply H; eauto.

  + edestruct IHexec.
    * eauto.
    * rewrite thread_upd_ne_comm; eauto.
    * intuition idtac.
      autorewrite with t in *.

      eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t; eauto.
        eauto.
        rewrite thread_upd_ne_comm; eauto.
Grab Existential Variables.
  all: exact tt.
Qed.

Lemma trace_incl_proof_helper :
  forall `(p1 : proc opT T) p2 `(op_step : OpSemantics opT State),
  (forall tid ts s s' result tr evs,
    exec_tid op_step tid s p1 s' result evs ->
    exec_prefix op_step s' (ts [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
      exec_prefix op_step s ts [[tid := Proc p2]] (prepend tid evs tr)) ->
  trace_incl op_step
    p1 p2.
Proof.
  unfold trace_incl, trace_incl_opt, trace_incl_ts.
  intros.

  eapply trace_incl_ts_s_proof_helper.
  eauto.
Qed.

Lemma trace_incl_s_proof_helper :
  forall `(p1 : proc opT T) p2 `(op_step : OpSemantics opT State) s tid,
  (forall ts s0 s' result tr evs,
    exec_others op_step tid s s0 ->
    exec_tid op_step tid s0 p1 s' result evs ->
    exec_prefix op_step s' (ts [[tid := match result with
                                 | inl _ => NoProc
                                 | inr p' => Proc p'
                                 end]]) tr ->
    exists tr',
      exec_prefix op_step s0 ts [[tid := Proc p2]] tr' /\
      prepend tid evs tr = tr') ->
  trace_incl_s s tid op_step
    p1 p2.
Proof.
  unfold trace_incl_s.
  intros.

  eapply trace_incl_ts_s_proof_helper.
  intros.
  eapply H in H2; eauto.
  propositional; auto.
Qed.

Theorem trace_incl_op :
  forall `(p : T -> proc opT T') op `(op_step : OpSemantics opT State),
  trace_incl op_step
    (Bind (Op op) p)
    (Bind (Atomic (Op op)) p).
Proof.
  intros.
  eapply trace_incl_proof_helper; intros.
  repeat exec_tid_inv.

  eapply ExecPrefixOne with (tid := tid).
    autorewrite with t; eauto.
    eauto 20.
    autorewrite with t; eauto.
Qed.

Ltac abstract_tr :=
  match goal with
  | |- exec_prefix _ _ _ ?tr => abstract_term tr
  end.

Theorem trace_incl_atomize_ret_l :
  forall `(f : T1 -> T2)
         `(p : proc opT T1)
         `(rx : _ -> proc opT TF)
         `(op_step : OpSemantics opT State),
  trace_incl op_step
    (Bind (Bind (Atomic p) (fun r => Ret (f r))) rx)
    (Bind (Atomic (Bind p (fun r => Ret (f r)))) rx).
Proof.
  intros.
  eapply trace_incl_proof_helper; intros.
  repeat exec_tid_inv.

  eapply trace_incl_ts_s_proof_helper in H0.
  abstract_tr.
  eapply ExecPrefixOne with (tid := tid).
    autorewrite with t; eauto.
    eauto.
    simpl. autorewrite with t. eauto.
  rewrite app_nil_r. eauto.

  intros.
  repeat exec_tid_inv.
  eauto.
Qed.

Theorem trace_incl_bind_a : forall `(p : proc opT T) `(p2 : T -> proc _ T') p2' `(op_step : OpSemantics opT State),
  (forall x, trace_incl op_step (p2 x) (p2' x)) ->
  trace_incl op_step (Bind p p2) (Bind p p2').
Proof.
  unfold trace_incl, trace_incl_opt,
         trace_incl_ts, trace_incl_ts_s.
  intros.

  match goal with
  | H : exec_prefix _ _ (thread_upd ?ts ?tid ?pp) _ |- _ =>
    remember (thread_upd ts tid pp);
    generalize dependent ts;
    generalize dependent p;
    unfold exec_prefix in H; repeat deex;
    induction H; intros; subst; eauto

  end.

  destruct (tid0 == tid); subst.
  + autorewrite with t in *.
    repeat maybe_proc_inv.
    exec_tid_inv.
    destruct result0.

    * edestruct H; eauto.
      intuition idtac.

      eapply ExecPrefixOne with (tid := tid).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.

    * edestruct IHexec; eauto.
      intuition idtac.

      eapply ExecPrefixOne with (tid := tid).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.

  + edestruct IHexec.
    rewrite thread_upd_ne_comm; eauto.
    intuition idtac.

    autorewrite with t in *.
    eapply ExecPrefixOne with (tid := tid0).
      autorewrite with t; eauto.
      eauto.
      rewrite thread_upd_ne_comm; eauto.
Qed.

Theorem trace_incl_s_bind_a : forall `(p : proc opT T) `(p2 : T -> proc _ T') p2' `(op_step : OpSemantics opT State) s tid,
  (forall s' x,
    exec_any op_step tid s p x s' ->
    trace_incl_s s' tid op_step (p2 x) (p2' x)) ->
  trace_incl_s s tid op_step (Bind p p2) (Bind p p2').
Proof.
  unfold trace_incl_s, trace_incl_ts_s.
  intros.

  match goal with
  | H : exec_prefix _ _ (thread_upd ?ts ?tid ?pp) _ |- _ =>
    remember (thread_upd ts tid pp);
    generalize dependent ts;
    generalize dependent p;
    destruct H as [? H];
    induction H; intros; subst; eauto
  end.

  destruct (tid0 == tid); subst.
  + autorewrite with t in *.
    repeat maybe_proc_inv.
    exec_tid_inv.
    destruct result0.

    * edestruct H2; eauto.
      intuition idtac.

      eapply ExecPrefixOne with (tid := tid).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.

    * edestruct IHexec; eauto.
      intuition idtac.

      eapply ExecPrefixOne with (tid := tid).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.

  + edestruct IHexec.
    eauto.
    rewrite thread_upd_ne_comm; eauto.
    intuition idtac.

    autorewrite with t in *.
    eapply ExecPrefixOne with (tid := tid0).
      autorewrite with t; eauto.
      eauto.
      rewrite thread_upd_ne_comm; eauto.

Grab Existential Variables.
  all: exact tt.
Qed.

Theorem trace_incl_N_bind_a : forall `(p : proc opT T) `(p2 : T -> proc _ T') p2' `(op_step : OpSemantics opT State) n,
  (forall x, trace_incl_N (n-1) op_step (p2 x) (p2' x)) ->
  trace_incl_N n op_step (Bind p p2) (Bind p p2').
Proof.
  unfold trace_incl_N, trace_incl_opt_N,
         trace_incl_ts_N, trace_incl_ts_s_N.
  intros.

  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid ?pp) _ _ |- _ =>
    remember (thread_upd ts tid pp);
    generalize dependent ts;
    generalize dependent p;
    induction H; intros; subst; eauto
  end.

  destruct (tid0 == tid); subst.
  + autorewrite with t in *.
    repeat maybe_proc_inv.
    exec_tid_inv.
    destruct result0.

    * edestruct H.
      2: eassumption.
      omega.
      intuition idtac.

      eapply ExecPrefixOne with (tid := tid).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.

    * edestruct IHexec.
      2: eauto.
      omega.
      intuition idtac.

      eapply ExecPrefixOne with (tid := tid).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t; eauto.

  + edestruct IHexec.
    omega.
    rewrite thread_upd_ne_comm; eauto.
    intuition idtac.

    autorewrite with t in *.
    eapply ExecPrefixOne with (tid := tid0).
      autorewrite with t; eauto.
      eauto.
      rewrite thread_upd_ne_comm; eauto.
Qed.

Instance trace_incl_opt_N_refl :
  Reflexive (@trace_incl_opt_N n opT State op_step).
Proof.
  unfold Reflexive; intros.
  unfold trace_incl_opt_N; intros.
  reflexivity.
Qed.

Instance trace_incl_N_refl :
  Reflexive (@trace_incl_N n opT T State op_step).
Proof.
  unfold Reflexive; intros.
  unfold trace_incl_N; intros.
  reflexivity.
Qed.

Instance trace_incl_rx_N_refl :
  Reflexive (@trace_incl_rx_N n opT T State op_step).
Proof.
  unfold Reflexive; intros.
  unfold trace_incl_rx_N; intros.
  eapply trace_incl_N_bind_a.
  eauto.
Qed.

Theorem trace_incl_N_le :
  forall `(op_step : OpSemantics opT State) T (p1 p2 : proc _ T) n1 n2,
    trace_incl_N n2 op_step p1 p2 ->
    n1 <= n2 ->
    trace_incl_N n1 op_step p1 p2.
Proof.
  repeat ( intro; intros ).
  eapply H in H2; try omega.
  eauto.
Qed.

Theorem trace_incl_rx_N_le :
  forall `(op_step : OpSemantics opT State) T (p1 p2 : proc _ T) n1 n2,
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

Instance trace_incl_rx_preorder :
  PreOrder (@trace_incl_rx opT T State op_step).
Proof.
  split.
  - unfold Reflexive; intros.
    unfold trace_incl_rx; intros.
    unfold trace_incl_rx_N; intros.
    eapply trace_incl_N_bind_a.
    eauto.
  - unfold Transitive; intros.
    unfold trace_incl_rx in *; intros.
    repeat ( intro; intros ).
    eapply H with (n := n') in H4; try omega.
    destruct H4.
    eapply H0 with (n := x0) in H4; try omega.
    eauto.
    2: intros; reflexivity.
    reflexivity. reflexivity.
    reflexivity. 2: reflexivity.
    intros; eapply trace_incl_N_le; eauto.
    omega.
Qed.

Instance Bind_trace_incl_proper_2 :
  Proper (eq ==>
          pointwise_relation T0 (@trace_incl opT T State op_step) ==>
          @trace_incl opT T State op_step) Bind.
Proof.
  intros.
  intros p1a p1b H1; subst.
  intros p2a p2b H2.
  eapply trace_incl_bind_a; intros.
  eapply H2.
Qed.

Lemma trace_incl_atomic_bind :
  forall `(p1 : proc opT T)
         `(p2 : T -> proc opT T2)
         `(p3 : T2 -> proc opT T3)
         `(op_step : OpSemantics opT State),
  trace_incl op_step
    (Bind (Atomic (Bind p1 p2)) p3)
    (Bind (Bind (Atomic p1) (fun r => Atomic (p2 r))) p3).
Proof.
  intros.
  eapply trace_incl_proof_helper; intros.
  repeat exec_tid_inv.
  atomic_exec_inv.

  abstract_tr.
  eapply ExecPrefixOne with (tid := tid).
    autorewrite with t; eauto.
    eauto.
    autorewrite with t.

  eapply ExecPrefixOne with (tid := tid).
    autorewrite with t; eauto.
    eauto.
    autorewrite with t.
  eauto.

  rewrite prepend_app. eauto.
Qed.

Lemma trace_incl_atomic :
  forall `(p1 : proc opT T)
         `(p2 : T -> proc opT T2)
         `(op_step : OpSemantics opT State),
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

  all: abstract_tr.
  all: try solve [ eapply ExecPrefixOne with (tid := tid);
                     [ autorewrite with t; eauto
                     | eauto
                     | autorewrite with t; eauto ];
                     eauto ].
  all: try reflexivity.

  rewrite prepend_app.
  rewrite exec_equiv_norx_bind_bind.
  eauto.
Qed.

Instance trace_incl_to_trace_incl_N :
  subrelation (@trace_incl opT T State op_step) (trace_incl_N n op_step).
Proof.
  unfold subrelation; intros.
  intro; intros.
  intro; intros.
  intro; intros.
  eapply exec_to_exec_prefix in H1.
  eapply H in H1.
  eauto.
Qed.

Theorem trace_incl_N_ret_bind :
  forall `(op_step : OpSemantics opT State) `(v : T) TF (rx1 rx2 : _ -> proc _ TF) n,
    (forall a, trace_incl_N (n - 1) op_step (rx1 a) (rx2 a)) ->
    trace_incl_N n op_step (Bind (Ret v) rx1) (Bind (Ret v) rx2).
Proof.
  repeat ( intro; intros ).
  match goal with
  | H : exec _ _ (thread_upd ?ts ?tid (Proc ?p)) _ _ |- _ =>
    remember (thread_upd ts tid (Proc p));
    generalize dependent ts;
    induction H; intros; subst; eauto
  end.

  destruct (tid0 == tid); subst; autorewrite with t in *.
  * repeat maybe_proc_inv.
    repeat exec_tid_inv.
    eapply H in H3; try omega.
    eapply ExecPrefixOne with (tid := tid).
      autorewrite with t; eauto.
      eauto.
      autorewrite with t; eauto.

  * edestruct IHexec.
      omega.
      rewrite thread_upd_ne_comm; eauto.

    eapply ExecPrefixOne with (tid := tid0).
      rewrite thread_upd_ne in * by auto. eauto.
      eauto.
    rewrite thread_upd_ne_comm by eauto.
    eauto.
Qed.

Theorem trace_incl_rx_until_helper :
  forall T opT (p1 p2 : option T -> proc opT T)
         `(op_step : OpSemantics opT State)
         (c : T -> bool) n v,
    (forall v', trace_incl_rx_N (n-1) op_step (p1 v') (p2 v')) ->
    trace_incl_rx_N n op_step (Until c p1 v) (Until c p2 v).
Proof.
  induction n; intros.

  - intro; intros.
    intro; intros.
    intro; intros.
    intro; intros.
    match goal with
    | H : exec _ _ _ _ _ |- _ =>
      inversion H; clear H; repeat sigT_eq; subst; eauto
    end.
    omega.

  - intro; intros.
    intro; intros.
    intro; intros.
    intro; intros.
    match goal with
    | H : exec _ _ _ _ _ |- _ =>
      inversion H; clear H; repeat sigT_eq; subst; eauto
    end.

    destruct (tid0 == tid); subst; autorewrite with t in *.

    + repeat maybe_proc_inv.
      repeat exec_tid_inv.

      unfold until1 in *.
      match goal with
      | H : exec _ _ _ _ _ |- _ =>
        eapply exec_equiv_N_bind_bind in H
      end.

      replace (S n - 1) with (n) in * by omega.

      match goal with
      | H : exec _ _ _ _ _,
        H' : forall _, trace_incl_rx_N _ _ _ _ |- _ =>
        eapply H' in H; try omega
      end.

      eapply ExecPrefixOne with (tid := tid).
        autorewrite with t; eauto.
        eauto.
        autorewrite with t.
        unfold until1.
        rewrite exec_equiv_bind_bind.
        eassumption.

      3: reflexivity.
      omega.

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

    + edestruct IHn.
        intros. eapply trace_incl_rx_N_le; eauto; omega.
        4: rewrite thread_upd_ne_comm in H6 by eauto; eassumption.
        3: reflexivity. omega.
        intros. eapply trace_incl_N_le; eauto; omega.

      eapply ExecPrefixOne with (tid := tid0).
        autorewrite with t; eauto.
        eassumption.
        rewrite thread_upd_ne_comm by eauto; eauto.
Qed.

Theorem trace_incl_rx_until :
  forall T opT (p1 p2 : option T -> proc opT T)
         `(op_step : OpSemantics opT State)
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

Theorem trace_incl_rx_to_trace_incl :
  forall `(op_step : OpSemantics opT State) T (p1 p2 : proc opT T),
    trace_incl_rx op_step p1 p2 ->
    forall `(rx : _ -> proc _ TF),
      trace_incl op_step (Bind p1 rx) (Bind p2 rx).
Proof.
  repeat ( intro; intros ).
  unfold exec_prefix in H0; deex.
  eapply H.
  3: reflexivity.
  3: eassumption.
  reflexivity.
  reflexivity.
Qed.

Theorem trace_incl_to_trace_incl_rx :
  forall `(op_step : OpSemantics opT State) T (p1 p2 : proc opT T),
    (forall `(rx : _ -> proc _ TF),
      trace_incl op_step (Bind p1 rx) (Bind p2 rx)) ->
    trace_incl_rx op_step p1 p2.
Proof.
  repeat ( intro; intros ).
  assert (trace_incl_rx op_step p1 p1) by reflexivity.
  eapply H4 in H3; [ | reflexivity | eassumption | omega ].
  edestruct H; try eassumption.
  eexists; intuition idtac.
  eassumption.
Qed.


(** Correspondence between different layers *)

Definition traces_match_ts {opLoT opMidT State} lo_step hi_step
                           (ts1 : @threads_state opLoT)
                           (ts2 : @threads_state opMidT) :=
  forall (s : State) tr1,
    exec_prefix lo_step s ts1 tr1 ->
      exec_prefix hi_step s ts2 tr1.

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
