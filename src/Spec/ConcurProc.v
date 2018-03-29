Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Morphisms.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Helpers.Helpers.
Require Import Helpers.ListStuff.
Require Import List.
Require Import Bool.

Import ListNotations.

Global Set Implicit Arguments.
Global Generalizable All Variables.


Section Trace.

  Inductive event :=
  | Event : forall T (v : T), event.

  Inductive trace :=
  | TraceEvent : forall (tid : nat) (ev : event), trace -> trace
  | TraceEmpty : trace.


  Fixpoint prepend tid (evs : list event) (tr : trace) : trace :=
    match evs with
    | nil => tr
    | e :: evs' =>
      TraceEvent tid e (prepend tid evs' tr)
    end.

End Trace.

Arguments Event {T}.


Section Proc.

  Variable opT : Type -> Type.
  Variable State : Type.

  Inductive proc : Type -> Type :=
  | Op : forall T (op : opT T), proc T
  | Ret : forall T (v : T), proc T
  | Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T
  | Until : forall T (c : T -> bool) (p : option T -> proc T) (v : option T), proc T
  | Atomic : forall T (p : proc T), proc T.


  Definition OpSemantics := forall T, opT T -> nat -> State -> T -> State -> list event -> Prop.
  Variable op_step : OpSemantics.


  Inductive maybe_proc :=
  | Proc : forall T, proc T -> maybe_proc
  | NoProc.

  Definition threads_state := list maybe_proc.

  Definition thread_get (ts : threads_state) (tid : nat) :=
    match nth_error ts tid with
    | Some x => x
    | None => NoProc
    end.

  Definition thread_upd (ts : threads_state) (tid : nat) (s : maybe_proc) : threads_state :=
    list_upd (pad ts (S tid) NoProc) tid s.


  Definition until1 T (c : T -> bool)
                      (p : option T -> proc T)
                      (v : option T) :=
    Bind (p v) (fun x => if bool_dec (c x) true then Ret x else Until c p (Some x)).


  Inductive atomic_exec : forall T, proc T -> nat -> State ->
                                    T -> State -> list event -> Prop :=

  | AtomicRet : forall T tid (v : T) s,
    atomic_exec (Ret v) tid s v s nil

  | AtomicBind : forall T1 T2 tid (p1 : proc T1) (p2 : T1 -> proc T2)
                        s0 s1 s2 ev1 ev2 (v1 : T1) (v2 : T2),
    atomic_exec p1 tid s0 v1 s1 ev1 ->
    atomic_exec (p2 v1) tid s1 v2 s2 ev2 ->
    atomic_exec (Bind p1 p2) tid s0 v2 s2 (ev1 ++ ev2)

  | AtomicOp : forall T tid (v : T) s s' op evs,
    op_step op tid s v s' evs ->
    atomic_exec (Op op) tid s v s' evs

  | AtomicUntil : forall T (p : option T -> proc T) (c : T -> bool) v tid s r s' ev',
    atomic_exec (until1 c p v) tid s r s' ev' ->
    atomic_exec (Until c p v) tid s r s' ev'
  .


  Inductive exec_tid : forall T (tid : nat),
    State -> proc T ->
    State -> T + proc T -> list event -> Prop :=

  | ExecTidRet : forall tid T (v : T) s,
    exec_tid tid s (Ret v)
                 s (inl v)
                 nil

  | ExecTidOp : forall tid T (v : T) s s' op evs,
    op_step op tid s v s' evs ->
    exec_tid tid s (Op op)
                 s' (inl v)
                 evs

  | ExecTidAtomic : forall tid T (v : T) ap s s' evs,
    atomic_exec ap tid s v s' evs ->
    exec_tid tid s (Atomic ap)
                 s' (inl v)
                 evs

  | ExecTidBind : forall tid T1 (p1 : proc T1) T2 (p2 : T1 -> proc T2) s s' result evs,
    exec_tid tid s p1
                 s' result evs ->
    exec_tid tid s (Bind p1 p2)
                 s' (inr
                     match result with
                     | inl r => p2 r
                     | inr p1' => Bind p1' p2
                     end
                    ) evs

  | ExecTidUntil : forall tid T (p : option T -> proc T) (c : T -> bool) v s,
    exec_tid tid s (Until c p v)
                 s (inr (until1 c p v))
                 nil.


  Inductive exec : State -> threads_state -> trace -> nat -> Prop :=

  | ExecOne : forall T tid (ts : threads_state) trace p s s' evs result ctr,
    thread_get ts tid = @Proc T p ->
    exec_tid tid s p s' result evs ->
    exec s' (thread_upd ts tid
              match result with
              | inl _ => NoProc
              | inr p' => Proc p'
              end) trace ctr ->
    exec s ts (prepend tid evs trace) (S ctr)

  | ExecExpired : forall (ts : threads_state) s,
    exec s ts TraceEmpty 0.


  Definition exec_prefix (s : State) (ts : threads_state) (tr : trace) : Prop :=
    exists n,
      exec s ts tr n.

  Theorem ExecPrefixOne
       : forall (T : Type) 
           (tid : nat) (ts : threads_state) (tr : trace)
           (p : proc T) (s s' : State)
           (evs : list event) (result : T + proc T),
         thread_get ts tid = Proc p ->
         exec_tid tid s p s' result evs ->
         exec_prefix s'
           (thread_upd ts tid
             (match result with
              | inl _ => NoProc
              | inr p' => Proc p'
              end)) tr ->
         exec_prefix s ts (prepend tid evs tr).
  Proof.
    unfold exec_prefix; intros; deex.
    eexists; eapply ExecOne; eauto.
  Qed.


  Theorem exec_to_exec_prefix : forall s ts tr ctr,
    exec s ts tr ctr ->
    exec_prefix s ts tr.
  Proof.
    unfold exec_prefix; eauto.
  Qed.


  Inductive exec_any (tid : nat) (s : State) :
    forall T (p : proc T) (r : T) (s' : State), Prop :=
  | ExecAnyOther :
    forall T (p : proc T) (r : T) (s' : State)
           T' (op' : opT T') tid' s0 r0 evs,
    tid <> tid' ->
    op_step op' tid' s r0 s0 evs ->
    exec_any tid s0 p r s' ->
    exec_any tid s p r s'
  | ExecAnyThisDone :
    forall T (p : proc T) (r : T) (s' : State) evs,
    exec_tid tid s p s' (inl r) evs ->
    exec_any tid s p r s'
  | ExecAnyThisMore :
    forall T (p p' : proc T) (s' s0 : State) r evs,
    exec_tid tid s p s0 (inr p') evs ->
    exec_any tid s0 p' r s' ->
    exec_any tid s p r s'
  .

  Definition exec_others (tid : nat) (s s' : State) : Prop :=
    clos_refl_trans_1n _
      (fun s0 s1 =>
        exists tid' `(op' : opT T') r' evs,
          tid' <> tid /\
          op_step op' tid' s0 r' s1 evs)
      s s'.

  Lemma exec_any_op : forall `(op : opT T) tid r s s',
    exec_any tid s (Op op) r s' ->
      exists s0 evs,
        exec_others tid s s0 /\
        op_step op tid s0 r s' evs.
  Proof.
    intros.
    remember (Op op).
    induction H; subst.
    - edestruct IHexec_any; eauto; intuition idtac.
      deex.
      do 2 eexists; split; eauto.
      econstructor; eauto.
      do 5 eexists; split; eauto.
    - exists s; eexists; split.
      eapply rt1n_refl.
      inversion H; subst; repeat sigT_eq; eauto.
    - inversion H.
  Qed.

  Lemma exec_others_trans :
    forall tid s0 s1 s2,
      exec_others tid s0 s1 ->
      exec_others tid s1 s2 ->
      exec_others tid s0 s2.
  Proof.
    induction 1; intros; eauto.
    intuition idtac.
    repeat deex.
    econstructor; eauto 20.
  Qed.

  Lemma exec_tid_exec_others :
    forall tid tid' `(p : proc T) s s' result evs,
      tid <> tid' ->
      exec_tid tid' s p s' result evs ->
      exec_others tid s s'.
  Proof.
    induction 2; intros; eauto;
      try solve [ constructor ].
    - econstructor; eauto 10.
      eapply rt1n_refl.
    - induction H0; intros; eauto 10;
        try solve [ constructor ].
      eapply exec_others_trans; eauto.
      econstructor; eauto 10.
      eapply rt1n_refl.
  Qed.

  Lemma exec_others_exec_any :
    forall tid s s' s'' `(p : proc T) v,
      exec_others tid s s' ->
      exec_any tid s' p v s'' ->
      exec_any tid s p v s''.
  Proof.
    induction 1; intros; eauto.
    repeat deex.
    intuition idtac.
    eapply ExecAnyOther; try eassumption.
    eauto.
  Qed.

End Proc.

Arguments Op {opT T}.
Arguments Ret {opT T}.
Arguments Bind {opT T T1}.
Arguments Until {opT T}.
Arguments Atomic {opT T}.

Arguments Proc {opT T}.
Arguments NoProc {opT}.

Arguments threads_state {opT}.

Hint Constructors exec.
Hint Constructors exec_any.
Hint Resolve exec_to_exec_prefix.
Hint Resolve exec_tid_exec_others.
Hint Resolve exec_others_exec_any.
Hint Resolve exec_others_trans.


Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 60, right associativity).

Notation "ts [[ tid ]]" := (thread_get ts tid)
  (at level 8, left associativity).

Notation "ts [[ tid := p ]]" := (thread_upd ts tid p)
  (at level 8, left associativity).


Section StepImpl.

  Hint Constructors exec_tid.
  Hint Constructors atomic_exec.

  Variable opT : Type -> Type.
  Variable State : Type.
  Variable op_step1 : OpSemantics opT State.
  Variable op_step2 : OpSemantics opT State.

  Variable StepImpl :
    forall `(op : opT TT) tid s r s' evs,
      op_step1 op tid s r s' evs ->
      op_step2 op tid s r s' evs.

  Theorem atomic_exec_step_impl :
    forall tid s `(p : proc _ T) s' r evs,
      atomic_exec op_step1 p tid s s' r evs ->
      atomic_exec op_step2 p tid s s' r evs.
  Proof.
    intros.
    induction H; eauto.
  Qed.

  Theorem exec_tid_step_impl :
    forall tid s `(p : proc _ T) s' r evs,
      exec_tid op_step1 tid s p s' r evs ->
      exec_tid op_step2 tid s p s' r evs.
  Proof.
    intros.
    induction H; eauto.
    eapply atomic_exec_step_impl in H; eauto.
  Qed.

  Theorem exec_any_impl :
    forall tid s `(p : proc _ T) s' r,
      exec_any op_step1 tid s p r s' ->
      exec_any op_step2 tid s p r s'.
  Proof.
    intros.
    induction H; eauto.
    eapply exec_tid_step_impl in H; eauto.
    eapply exec_tid_step_impl in H; eauto.
  Unshelve.
    all: intros; eauto.
    all: try exact true.
    all: try exact None.
    exact (Ret r0).
  Qed.

End StepImpl.


Definition threads_empty {opT} : @threads_state opT := nil.


Lemma nth_error_nil : forall T x,
  nth_error (@nil T) x = None.
Proof.
  induction x; simpl; eauto.
Qed.

Lemma pad_eq : forall n `(ts : @threads_state opT) tid,
  ts [[ tid ]] = (pad ts n NoProc) [[ tid ]].
Proof.
  unfold thread_get.
  induction n; simpl; eauto.
  destruct ts.
  - destruct tid; simpl; eauto.
    rewrite <- IHn. rewrite nth_error_nil. auto.
  - destruct tid; simpl; eauto.
Qed.

Lemma pad_length_noshrink : forall n `(l : list T) v,
  length l <= length (pad l n v).
Proof.
  intros.
  generalize dependent l.
  induction n; simpl; eauto.
  destruct l; simpl; eauto.
  - specialize (IHn []). omega.
  - specialize (IHn l). omega.
Qed.

Lemma pad_length_grow : forall n `(l : list T) v,
  n <= length (pad l n v).
Proof.
  intros.
  generalize dependent l.
  induction n; simpl; intros; try omega.
  destruct l; simpl; eauto.
  - specialize (IHn []). omega.
  - specialize (IHn l). omega.
Qed.

Lemma pad_length_noshrink' : forall x n `(l : list T) v,
  x <= length l ->
  x <= length (pad l n v).
Proof.
  intros.
  pose proof (pad_length_noshrink n l v).
  omega.
Qed.

Lemma pad_noop : forall n T (l : list T) v,
  n <= length l ->
  pad l n v = l.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl in *.
  omega.
  rewrite IHn; eauto.
  omega.
Qed.

Lemma thread_get_Some_length : forall tid `(ts : @threads_state opT) `(p : proc _ T),
  ts [[ tid ]] = Proc p ->
  tid < length ts.
Proof.
  unfold thread_get.
  induction tid; simpl; intros.
  - destruct ts; try congruence. simpl. omega.
  - destruct ts; try congruence. simpl.
    specialize (IHtid _ _ _ _ H).
    omega.
Qed.

Lemma length_hint_lt_le : forall n m,
  S n <= m ->
  n < m.
Proof.
  intros; omega.
Qed.

Hint Resolve pad_length_noshrink.
Hint Resolve pad_length_grow.
Hint Resolve length_hint_lt_le.
Hint Resolve pad_length_noshrink'.
Hint Resolve thread_get_Some_length.
Hint Resolve lt_le_S.


Lemma prepend_app : forall `(evs1 : list event) evs2 tr tid,
  prepend tid (evs1 ++ evs2) tr = prepend tid evs1 (prepend tid evs2 tr).
Proof.
  induction evs1; simpl; intros; eauto.
  rewrite IHevs1; eauto.
Qed.

Lemma list_upd_eq : forall tid `(ts : @threads_state opT) p,
  tid < length ts ->
  (list_upd ts tid p) [[ tid ]] = p.
Proof.
  unfold thread_get.
  induction tid; simpl; intros; eauto.
  - destruct ts; simpl in *; eauto. omega.
  - destruct ts; simpl in *. omega.
    eapply IHtid. omega.
Qed.

Lemma list_upd_ne : forall tid' tid `(ts : @threads_state opT) p,
  tid < length ts ->
  tid' <> tid ->
  (list_upd ts tid p) [[ tid' ]] = ts [[ tid' ]].
Proof.
  unfold thread_get.
  induction tid'; simpl; intros; eauto.
  - destruct tid; try congruence.
    destruct ts; simpl in *. congruence.
    auto.
  - destruct ts; simpl in *. congruence.
    destruct tid; auto.
    eapply IHtid'. omega. omega.
Qed.

Lemma list_upd_noop : forall tid `(ts : @threads_state opT) `(p : proc _ T),
  ts [[ tid ]] = Proc p ->
  list_upd ts tid (Proc p) = ts.
Proof.
  unfold thread_get.
  induction tid; simpl; intros.
  - destruct ts; try congruence. simpl. congruence.
  - destruct ts; try congruence. simpl. f_equal. eauto.
Qed.

Lemma list_upd_noop_NoProc : forall tid `(ts : @threads_state opT),
  ts [[ tid ]] = NoProc ->
  tid < length ts ->
  list_upd ts tid NoProc = ts.
Proof.
  unfold thread_get.
  induction tid; simpl; intros.
  - destruct ts; try congruence. simpl. congruence.
    simpl. subst. congruence.
  - destruct ts; try congruence. simpl. congruence.
    simpl. f_equal. eapply IHtid. 2: simpl in *; omega.
    eauto.
Qed.

Lemma thread_upd_same : forall tid `(ts : @threads_state opT) `(p : proc _ T),
  ts [[ tid ]] = Proc p ->
  ts [[ tid := Proc p ]] = ts.
Proof.
  unfold thread_upd; intros.
  rewrite pad_noop by eauto.
  rewrite list_upd_noop; eauto.
Qed.

Lemma thread_upd_same' : forall tid `(ts : @threads_state opT),
  tid < length ts ->
  ts [[ tid ]] = NoProc ->
  ts [[ tid := NoProc ]] = ts.
Proof.
  unfold thread_upd; intros.
  rewrite pad_noop by eauto.
  rewrite list_upd_noop_NoProc; eauto.
Qed.

Lemma thread_upd_eq : forall tid `(ts : @threads_state opT) p,
  ts [[ tid := p ]] [[ tid ]] = p.
Proof.
  unfold thread_upd; intros.
  apply list_upd_eq.
  pose proof (pad_length_grow (S tid) ts NoProc).
  omega.
Qed.

Lemma thread_get_pad : forall tid `(ts : @threads_state opT) n,
  (pad ts n NoProc) [[ tid ]] = ts [[ tid ]].
Proof.
  unfold thread_get.
  induction tid; simpl.
  - destruct ts; simpl.
    destruct n; simpl; eauto.
    destruct n; simpl; eauto.
  - destruct ts; simpl; eauto.
    + destruct n; simpl; eauto. rewrite IHtid. rewrite nth_error_nil. auto.
    + destruct n; simpl; eauto.
Qed.

Lemma thread_upd_ne : forall tid `(ts : @threads_state opT) p tid',
  tid <> tid' ->
  ts [[ tid := p ]] [[ tid' ]] = ts [[ tid' ]].
Proof.
  unfold thread_upd.
  intros.
  rewrite list_upd_ne; auto.
  rewrite thread_get_pad. eauto.
Qed.

Lemma list_upd_pad : forall `(ts : @threads_state opT) tid n p,
  tid < length ts ->
  pad (list_upd ts tid p) n NoProc = list_upd (pad ts n NoProc) tid p.
Proof.
  induction ts; simpl; intros.
  - omega.
  - destruct tid; simpl.
    + destruct n; simpl; eauto.
    + destruct n; simpl; eauto.
      f_equal.
      eapply IHts.
      omega.
Qed.

Lemma list_upd_comm : forall `(ts : @threads_state opT) tid1 p1 tid2 p2,
  tid1 < length ts ->
  tid2 < length ts ->
  tid1 <> tid2 ->
  list_upd (list_upd ts tid1 p1) tid2 p2 = list_upd (list_upd ts tid2 p2) tid1 p1.
Proof.
  induction ts; simpl; intros; eauto.
  - destruct tid1; destruct tid2; try omega; simpl; eauto.
    f_equal. apply IHts; omega.
Qed.

Lemma list_upd_upd_eq : forall `(ts : @threads_state opT) tid p1 p2,
  tid < length ts ->
  list_upd (list_upd ts tid p1) tid p2 = list_upd ts tid p2.
Proof.
  induction ts; simpl; eauto; intros.
  destruct tid; simpl; eauto.
  f_equal.
  eapply IHts.
  omega.
Qed.

Lemma pad_comm : forall T n m (l : list T) v,
  pad (pad l n v) m v = pad (pad l m v) n v.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl; eauto.
  - destruct m; simpl; eauto. rewrite IHn. eauto.
  - destruct m; simpl; eauto. rewrite IHn; eauto.
Qed.

Lemma pad_idem : forall T n (l : list T) v,
  pad (pad l n v) n v = pad l n v.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; simpl; eauto.
  - rewrite IHn. eauto.
  - rewrite IHn. eauto.
Qed.

Lemma thread_upd_upd_ne : forall tid tid' `(ts : @threads_state opT) p p',
  tid <> tid' ->
  ts [[ tid := p ]] [[ tid' := p' ]] =
  ts [[ tid' := p' ]] [[ tid := p ]].
Proof.
  unfold thread_upd.
  intros.
  repeat rewrite list_upd_pad by eauto.
  rewrite list_upd_comm by eauto.
  f_equal.
  f_equal.
  apply pad_comm.
Qed.

Lemma thread_upd_upd_eq : forall tid `(ts : @threads_state opT) p1 p2,
  ts [[ tid := p1 ]] [[ tid := p2 ]] =
  ts [[ tid := p2 ]].
Proof.
  unfold thread_upd; intros.
  rewrite list_upd_pad by eauto.
  rewrite pad_idem.
  rewrite list_upd_upd_eq by eauto.
  reflexivity.
Qed.

Lemma thread_upd_inv : forall `(ts : @threads_state opT) tid1 `(p : proc _ T) tid2 `(p' : proc _ T'),
  ts [[ tid1 := Proc p ]] [[ tid2 ]] = Proc p' ->
  tid1 = tid2 /\ Proc p = Proc p' \/
  tid1 <> tid2 /\ ts [[ tid2 ]] = Proc p'.
Proof.
  intros.
  destruct (tid1 == tid2).
  - left; intuition eauto; subst.
    rewrite thread_upd_eq in H. congruence.
  - right; intuition eauto.
    rewrite thread_upd_ne in H; eauto.
Qed.

Lemma thread_empty_inv : forall opT tid `(p' : proc _ T),
  (@threads_empty opT) [[ tid ]] = Proc p' ->
  False.
Proof.
  unfold threads_empty; intros.
  destruct tid; compute in H; congruence.
Qed.

Lemma thread_get_S : forall `(ts : @threads_state opT) tid a,
  (a :: ts) [[ S tid ]] = ts [[ tid ]].
Proof.
  reflexivity.
Qed.

Lemma thread_get_0 : forall `(ts : @threads_state opT) a,
  (a :: ts) [[ 0 ]] = a.
Proof.
  reflexivity.
Qed.

Lemma thread_upd_S : forall `(ts : @threads_state opT) tid a p,
  (a :: ts) [[ S tid := p ]] = a :: (ts [[ tid := p ]]).
Proof.
  reflexivity.
Qed.

Lemma thread_upd_0 : forall `(ts : @threads_state opT) a p,
  (a :: ts) [[ 0 := p ]] = p :: ts.
Proof.
  reflexivity.
Qed.

Lemma thread_get_nil : forall opT tid,
  @thread_get opT nil tid = NoProc.
Proof.
  unfold thread_get; intros.
  rewrite nth_error_nil.
  reflexivity.
Qed.

Lemma thread_upd_nil_S : forall opT tid p,
  @thread_upd opT nil (S tid) p = NoProc :: (nil [[ tid := p ]]).
Proof.
  reflexivity.
Qed.

Lemma length_thread_upd : forall tid `(ts : @threads_state opT) p,
  length (ts [[ tid := p ]]) = Nat.max (S tid) (length ts).
Proof.
  induction tid; simpl; intros.
  - destruct ts; cbn; eauto.
  - destruct ts.
    + rewrite thread_upd_nil_S.
      simpl length. rewrite IHtid.
      simpl. omega.
    + rewrite thread_upd_S.
      simpl length. rewrite IHtid.
      simpl. omega.
Qed.

Lemma thread_get_repeat_NoProc : forall opT n tid,
  (repeat (@NoProc opT) n) [[ tid ]] = NoProc.
Proof.
  induction n; simpl; intros.
  - rewrite thread_get_nil. eauto.
  - destruct tid.
    + rewrite thread_get_0. eauto.
    + rewrite thread_get_S. eauto.
Qed.

Lemma thread_upd_same'' : forall tid `(ts : @threads_state opT),
  tid >= length ts ->
  ts [[ tid := NoProc ]] = pad ts (S tid) NoProc.
Proof.
  unfold thread_upd; intros.
  rewrite list_upd_noop_NoProc; eauto.
  rewrite pad_is_append.

  generalize dependent tid.
  induction ts; intros.
  - rewrite app_nil_l.
    rewrite thread_get_repeat_NoProc. eauto.
  - destruct tid.
    + simpl in *. omega.
    + simpl app. rewrite thread_get_S. eapply IHts. simpl in *. omega.
Qed.

Lemma thread_get_oob : forall tid `(ts : @threads_state opT),
  tid >= length ts ->
  ts [[ tid ]] = NoProc.
Proof.
  induction tid; simpl; intros.
  - destruct ts; simpl in *; eauto.
    omega.
  - destruct ts.
    rewrite thread_get_nil; eauto.
    rewrite thread_get_S. eapply IHtid.
    simpl in *; omega.
Qed.

Hint Rewrite thread_upd_upd_eq : t.
Hint Rewrite thread_upd_eq : t.
Hint Rewrite thread_upd_ne using (solve [ auto ]) : t.

Hint Extern 1 (exec_tid _ _ _ _ _ _ _) => econstructor.
Hint Extern 1 (atomic_exec _ _ _ _ _ _ _) => econstructor.


Lemma thread_get_app_NoProc : forall `(ts : @threads_state opT) tid `(p : proc _ T),
  ts [[ tid ]] = Proc p <->
  (ts ++ [NoProc]) [[ tid ]] = Proc p.
Proof.
  split; intros.
  - generalize dependent tid.
    induction ts; simpl; intros.
    + exfalso.
      unfold thread_get in H.
      rewrite nth_error_nil in H.
      congruence.
    + destruct tid; cbn in *; eauto.
  - generalize dependent tid.
    induction ts; simpl; intros.
    + destruct tid; cbn in *.
      congruence.
      rewrite thread_get_S in H.
      exfalso.
      unfold thread_get in H.
      rewrite nth_error_nil in H.
      congruence.
    + destruct tid; cbn in *; eauto.
Qed.

Lemma thread_upd_app_NoProc : forall `(ts : @threads_state opT) tid p,
  tid < length ts ->
  ts [[ tid := p ]] ++ [NoProc] = (ts ++ [NoProc]) [[ tid := p ]].
Proof.
  induction ts; simpl; intros; try omega.
  destruct tid.
  - repeat rewrite thread_upd_0.
    reflexivity.
  - repeat rewrite thread_upd_S.
    simpl; f_equal.
    rewrite IHts; auto.
    omega.
Qed.


Ltac maybe_proc_inv := match goal with
  | H : ?a = ?a |- _ =>
    clear H
  | H : Proc _ = Proc _ |- _ =>
    inversion H; clear H; subst
  | H : existT _ _ _ = existT _ _ _ |- _ =>
    sigT_eq
  | H : existT _ _ _ = existT _ _ _ |- _ =>
    inversion H; clear H; subst
  end.

Ltac exec_tid_inv :=
  match goal with
  | H : exec_tid _ _ _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat maybe_proc_inv
  end;
  autorewrite with t in *.

Ltac atomic_exec_inv :=
  match goal with
  | H : atomic_exec _ _ _ _ _ _ _ |- _ =>
    inversion H; clear H; subst; repeat maybe_proc_inv
  end;
  autorewrite with t in *.
