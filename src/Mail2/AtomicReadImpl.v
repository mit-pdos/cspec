Require Import POCS.
Require Import String.
Require Import MailboxAPI.
Require Import FMapFacts.


Instance key_elt_equiv : Equivalence (MailboxAPI.Dir.eq_key_elt (elt:=string)).
Proof.
  split; intro; intros.
  - constructor; eauto.
  - inversion H. constructor; eauto.
  - inversion H. inversion H0. constructor; congruence.
Qed.

Hint Resolve key_elt_equiv.


Module AtomicReader <: LayerImpl MailboxAPI AtomicMailboxAPI.

  Definition deliver_core (m : string) :=
    _ <- Op (MailboxAPI.Deliver m);
    Ret tt.

  Fixpoint read_list (l : list string) (r : list string) :=
    match l with
    | nil => Ret r
    | fn :: l' =>
      m <- Op (MailboxAPI.Read fn);
      read_list l' (r ++ (m :: nil))
    end.

  Definition readall_core :=
    l <- Op MailboxAPI.List;
    read_list l nil.

  Definition compile_op T (op : AtomicMailboxAPI.opT T) : proc _ T :=
    match op with
    | AtomicMailboxAPI.Deliver m => deliver_core m
    | AtomicMailboxAPI.ReadAll => readall_core
    end.

  Ltac step_inv :=
    match goal with
    | H : MailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : AtomicMailboxAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (AtomicMailboxAPI.step _ _ _ _ _ _) => econstructor.

  Module DirFacts := WFacts_fun String_as_OT MailboxAPI.Dir.

  Lemma read_left_mover : forall fn,
    left_mover_pred
      MailboxAPI.step
      (MailboxAPI.Read fn)
      (fun tid s => MailboxAPI.Dir.In fn s).
  Proof.
    split.
    - unfold enabled_stable, enabled_in; intros; repeat deex.
      repeat step_inv; eauto.
      destruct (fn0 == fn); subst; try congruence.
      + exfalso. eapply H11. eexists. eauto.
      + do 3 eexists; econstructor.
        eapply MailboxAPI.Dir.add_2; eauto.
    - intros; repeat step_inv; eauto; repeat deex.
      destruct (fn0 == fn); subst; try congruence.
      eapply MailboxAPI.Dir.add_3 in H2; eauto.
  Qed.

  Hint Resolve read_left_mover.

  Theorem deliver_atomic : forall `(rx : _ -> proc _ T) m,
    trace_incl MailboxAPI.step
      (Bind (compile_op (AtomicMailboxAPI.Deliver m)) rx)
      (Bind (atomize compile_op (AtomicMailboxAPI.Deliver m)) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold deliver_core, ysa_movers.
    eauto.
  Qed.

  Lemma mailbox_fn_monotonic :
    forall s s' tid fn,
      exec_others MailboxAPI.step tid s s' ->
      MailboxAPI.Dir.In fn s ->
      MailboxAPI.Dir.In fn s'.
  Proof.
    induction 1; eauto; intros.
    repeat deex.
    eapply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
    clear H0.
    step_inv.
    eapply DirFacts.add_in_iff.
    eauto.
  Qed.

  Theorem readall_atomic : forall `(rx : _ -> proc _ T),
    trace_incl MailboxAPI.step
      (Bind (compile_op AtomicMailboxAPI.ReadAll) rx)
      (Bind (atomize compile_op AtomicMailboxAPI.ReadAll) rx).
  Proof.
    intros.
    eapply trace_incl_atomize_ysa.
    simpl.
    unfold readall_core, ysa_movers.
    eapply RightMoversDone.
    eapply OneNonMover.

    intros.
    eapply left_movers_impl with
      (P1 := fun tid s => Forall (fun fn => MailboxAPI.Dir.In fn s) r).

    {
      generalize (@nil string).
      induction r; simpl; eauto.
      constructor; eauto.

      - eapply left_mover_pred_impl; eauto.
        intros.
        inversion H; clear H; subst.
        eauto.

      - intros.
        inversion H; clear H; subst.
        eapply DirFacts.elements_in_iff in H2; deex.
        eapply MailboxAPI.Dir.elements_2 in H.
        do 2 eexists; econstructor; eauto.

      - intros.
        eapply left_movers_impl; eauto.
        intros; repeat deex.
        inversion H; clear H; subst.

        eapply exec_any_op in H0; repeat deex.
        step_inv.

        eapply Forall_impl; eauto; intros; simpl in *.
        eapply mailbox_fn_monotonic; eauto.
        eapply mailbox_fn_monotonic; eauto.
    }

    intros; repeat deex.
    eapply exec_any_op in H0; repeat deex.
    step_inv.
    eapply Forall_in'; intros.

    eapply mailbox_fn_monotonic; eauto.
    eapply DirFacts.elements_in_iff.

    eapply in_map_iff in H2; deex.
    destruct x0; simpl in *.

    eexists.
    eapply In_InA; eauto.
  Qed.

  Lemma read_list_exec : forall l l0 r s s' evs v tid,
    List.Forall (fun fn => MailboxAPI.Dir.In fn s) l ->
    Forall2 (fun fn m => MailboxAPI.Dir.MapsTo fn m s) l0 r ->
    atomic_exec MailboxAPI.step
      (read_list l r) tid
      s v s' evs ->
    s' = s /\ evs = nil /\
    Forall2 (fun fn m => MailboxAPI.Dir.MapsTo fn m s) (l0 ++ l) v.
  Proof.
    induction l; intros.
    - atomic_exec_inv.
      rewrite app_nil_r.
      eauto.
    - atomic_exec_inv.
      inversion H11; clear H11; subst; repeat sigT_eq.
      edestruct IHl; [ | | eauto | ]; step_inv.
      + inversion H; subst; eauto.
      + eapply Forall2_app; eauto.
      + rewrite <- app_assoc in H3; simpl in *.
        eauto.
  Qed.

  Theorem my_compile_correct :
    compile_correct compile_op MailboxAPI.step AtomicMailboxAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    + repeat atomic_exec_inv.
      simpl; intuition eauto.
      repeat step_inv; eauto.

    + atomic_exec_inv.
      eapply read_list_exec with (l0 := nil) in H10.
      {
        simpl in *.
        atomic_exec_inv.
        step_inv; subst; eauto.
        econstructor.

        assert (List.Forall (fun '(k, v) => MailboxAPI.Dir.MapsTo k v s1)
                  (MailboxAPI.Dir.elements s1)).
        {
          eapply Forall_forall; intros.
          destruct x.
          eapply MailboxAPI.Dir.elements_2.
          eapply In_InA; eauto.
        }

        generalize dependent (MailboxAPI.Dir.elements s1); intros.
        generalize dependent v.
        induction l; intros.
        - inversion H2; eauto.
        - inversion H2; clear H2; subst.
          inversion H; clear H; subst.
          specialize (IHl H4 _ H5); subst.
          destruct a; simpl in *; f_equal.
          eapply DirFacts.MapsTo_fun; eauto.
      }

      clear H10.
      atomic_exec_inv.
      step_inv.

      eapply Forall_forall; intros.
      eapply in_map_iff in H; deex.
      destruct x0.
      eapply DirFacts.elements_in_iff; eexists.
      eapply In_InA; eauto.

      eauto.
  Qed.

  Theorem my_atomize_correct :
    atomize_correct compile_op MailboxAPI.step.
  Proof.
    unfold atomize_correct; intros.
    destruct op.
    + rewrite deliver_atomic.
      eapply trace_incl_bind_a.
      eauto.
    + rewrite readall_atomic.
      eapply trace_incl_bind_a.
      eauto.
  Qed.

  Hint Resolve my_compile_correct.
  Hint Resolve my_atomize_correct.

  Theorem all_traces_match :
    forall ts1 ts2,
      proc_match (Compile.compile_ok compile_op) ts1 ts2 ->
      traces_match_ts MailboxAPI.step AtomicMailboxAPI.step ts1 ts2.
  Proof.
    intros.
    eapply Compile.compile_traces_match_ts; eauto.
  Qed.

  Definition absR (s1 : MailboxAPI.State) (s2 : AtomicMailboxAPI.State) :=
    s1 = s2.

  Definition compile_ts := Compile.compile_ts compile_op.

  Lemma read_list_no_atomics : forall l r,
    no_atomics (read_list l r).
  Proof.
    induction l; simpl; eauto.
  Qed.

  Hint Resolve read_list_no_atomics.

  Theorem compile_ts_no_atomics :
    forall ts,
      no_atomics_ts ts ->
      no_atomics_ts (compile_ts ts).
  Proof.
    eapply Compile.compile_ts_no_atomics.
    destruct op; compute; eauto.
  Qed.

  Theorem compile_traces_match :
    forall ts2,
      no_atomics_ts ts2 ->
      traces_match_abs absR MailboxAPI.initP MailboxAPI.step AtomicMailboxAPI.step (compile_ts ts2) ts2.
  Proof.
    unfold traces_match_abs; intros.
    rewrite H2 in *; clear H2.
    eapply all_traces_match; eauto.
    eapply Compile.compile_ts_ok; eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailboxAPI.initP s1 ->
      absR s1 s2 ->
      AtomicMailboxAPI.initP s2.
  Proof.
    eauto.
  Qed.

End AtomicReader.
