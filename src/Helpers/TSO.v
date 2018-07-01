Require Import ProofAutomation.
Require Import Helpers.FunMap.
Require Import Helpers.ListStuff.
Require Import Helpers.Instances.
Require Import Relations.Relation_Operators.
Require Import FunctionalExtensionality.

Import List.
Import List.ListNotations.
Open Scope list.

Section TSOModel.

  Variable T : Type.

  Record memT := mkMem {
    MemValue : T;
    SBuf : funmap nat (list T);
  }.

  Definition mem_read (m : memT) (tid : nat) : T :=
    match SBuf m tid with
    | nil => MemValue m
    | v :: _ => v
    end.

  Definition mem_write (v : T) (m : memT) (tid : nat) : memT :=
    mkMem (MemValue m) (fupd tid (v :: SBuf m tid) (SBuf m)).

  Definition mem_flush (m : memT) (tid : nat) : memT :=
    match SBuf m tid with
    | nil => m
    | v :: _ => mkMem v (fupd tid nil (SBuf m))
    end.

  Definition mem_bgflush (m : memT) (tid : nat) : memT :=
    mkMem (last (SBuf m tid) (MemValue m))
          (fupd tid (removelast (SBuf m tid)) (SBuf m)).

  Definition mem_bg : memT -> memT -> Prop :=
    clos_refl_trans_n1 memT (fun m m' => exists tid, m' = mem_bgflush m tid).

  Theorem mem_bg_trans : forall s1 s2 s3,
      mem_bg s1 s2 ->
      mem_bg s2 s3 ->
      mem_bg s1 s3.
  Proof.
    intros.
    apply Operators_Properties.clos_rtn1_rt in H.
    apply Operators_Properties.clos_rtn1_rt in H0.
    apply Operators_Properties.clos_rt_rtn1.
    econstructor 3; eauto.
  Qed.

  Lemma memT_eq : forall m1 m2,
      m1.(MemValue) = m2.(MemValue) ->
      (forall tid, m1.(SBuf) tid = m2.(SBuf) tid) ->
      m1 = m2.
  Proof.
    destruct m1, m2; simpl; intros; subst.
    f_equal.
    apply functional_extensionality; auto.
  Qed.

  Lemma mem_bgflush_write_commute_ne : forall m tid tid' v,
      tid <> tid' ->
      mem_write v (mem_bgflush m tid) tid' =
      mem_bgflush (mem_write v m tid') tid.
  Proof.
    intros.
    apply memT_eq; simpl; intros.
    rewrite fupd_ne by auto; auto.
    rewrite fupd_fupd_ne by auto.
    destruct (tid0 == tid); subst;
      rewrite ?fupd_eq, ?fupd_ne by congruence;
      auto.
    rewrite (fupd_ne (a:=tid) (a':=tid0)) by congruence.
    destruct (tid' == tid0); subst;
      rewrite ?fupd_eq, ?fupd_ne by congruence; auto.
  Qed.

  Lemma mem_bgflush_noop : forall m tid,
      m.(SBuf) tid = [] ->
      mem_bgflush m tid = m.
  Proof.
    unfold mem_bgflush; intros.
    rewrite H; simpl.
    apply memT_eq; simpl; intros; auto.
    destruct (tid == tid0); subst.
    rewrite fupd_eq; auto.
    rewrite fupd_ne; auto.
  Qed.

  Lemma last_prepend_nonempty : forall A (l: list A) (x:A) def,
      l <> [] ->
      last (x::l) def = last l def.
  Proof.
    induction l; simpl; congruence.
  Qed.

  Lemma removelast_prepend_nonempty : forall A (l: list A) (x:A),
      l <> [] ->
      x :: removelast l = removelast (x::l).
  Proof.
    induction l; simpl; congruence.
  Qed.

  Theorem mem_bg_transform_commute : forall m1 m2 m3 (f: memT -> memT),
      (* This is a cool condition! I wonder what it means. *)
      (forall m tid, mem_bg (f m) (f (mem_bgflush m tid))) ->
      mem_bg m1 m2 ->
      mem_bg (f m2) m3 ->
      mem_bg (f m1) m3.
  Proof.
    induction 2; simpl; intros; eauto.
    deex.
    apply IHclos_refl_trans_n1.
    eauto using mem_bg_trans.
  Qed.

  Lemma mem_bgflush_write_commute_nonempty : forall m tid v,
      m.(SBuf) tid <> [] ->
      mem_write v (mem_bgflush m tid) tid =
      mem_bgflush (mem_write v m tid) tid.
  Proof.
    unfold mem_bgflush, mem_write.
    destruct m; simpl; intros.
    autorewrite with fupd.
    rewrite last_prepend_nonempty,
    removelast_prepend_nonempty by auto.
    auto.
  Qed.

  Lemma mem_bg_commute_write : forall m1 m2 m3 m4 v tid,
      mem_bg m1 m2 ->
      m3 = mem_write v m2 tid ->
      mem_bg m3 m4 ->
      mem_bg (mem_write v m1 tid) m4.
  Proof.
    intros; subst.
    eapply mem_bg_transform_commute with
        (f := fun m => mem_write v m tid);
      intros; eauto.
    destruct (tid == tid0); subst.
    - destruct_with_eqn (m.(SBuf) tid0).
      rewrite mem_bgflush_noop by auto; constructor.
      apply Operators_Properties.clos_rtn1_step.
      exists tid0.
      apply mem_bgflush_write_commute_nonempty; congruence.
    - apply Operators_Properties.clos_rtn1_step.
      exists tid0.
      apply mem_bgflush_write_commute_ne; auto.
  Qed.

  Lemma mem_flush_bgflush_eq : forall m tid,
      mem_flush (mem_bgflush m tid) tid =
      mem_flush m tid.
  Proof.
    unfold mem_flush, mem_bgflush.
    destruct m; simpl; intros.
    autorewrite with fupd.
    destruct_with_eqn (SBuf0 tid); simpl.
    rewrite fupd_same by auto; auto.
    destruct l; auto.
  Qed.

  Lemma mem_flush_bgflush_ne_commute : forall m tid tid',
      tid <> tid' ->
      mem_flush (mem_bgflush m tid) tid' =
      mem_bgflush (mem_flush m tid') tid.
  Proof.
    unfold mem_flush, mem_bgflush.
    destruct m; simpl; intros.
    autorewrite with fupd.
    destruct_with_eqn (SBuf0 tid'); simpl; auto.
    rewrite fupd_ne by auto.
    apply memT_eq; simpl.
    (* oops, this isn't true - a bgflush before flush is overwritten, whereas a
    bgflush after remains in memory *)
  Abort.

  Definition empty_sb (m:memT) := forall tid, m.(SBuf) tid = [].

  Theorem empty_sb_mem_bgflush_noop : forall m tid,
      empty_sb m ->
      mem_bgflush m tid = m.
  Proof.
    unfold empty_sb, mem_bgflush; intros.
    apply memT_eq; simpl; intros.
    rewrite H; auto.
    rewrite H; simpl.
    rewrite fupd_same; auto.
  Qed.

  Theorem empty_sb_mem_bg_noop : forall m m',
      empty_sb m ->
      mem_bg m m' ->
      m' = m.
  Proof.
    induction 2; simpl; repeat deex;
      auto using empty_sb_mem_bgflush_noop.
  Qed.

  Theorem empty_sb_flush_noop : forall m tid,
      empty_sb m ->
      mem_flush m tid = m.
  Proof.
    unfold empty_sb, mem_flush; intros.
    apply memT_eq; simpl; intros.
    rewrite H; auto.
    rewrite H; auto.
  Qed.

  Theorem empty_sb_mem_read : forall m tid,
      empty_sb m ->
      mem_read m tid = m.(MemValue).
  Proof.
    unfold empty_sb, mem_read; intros.
    rewrite H; auto.
  Qed.

  Definition single_value (m:memT) tid v :=
    (forall tid', tid <> tid' -> m.(SBuf) tid' = []) /\
    mem_read m tid = v.

  Hint Unfold empty_sb single_value
       mem_read mem_write mem_bgflush : sb.

  Theorem empty_sb_single_value : forall m,
      empty_sb m ->
      forall tid, single_value m tid m.(MemValue).
  Proof.
    autounfold with sb; simpl; intuition eauto.
    rewrite H; auto.
  Qed.

  Theorem mem_write_single_value : forall m tid v0 v,
      single_value m tid v0 ->
      single_value (mem_write v m tid) tid v.
  Proof.
    autounfold with sb;
      simpl; (intuition idtac);
      autorewrite with fupd;
      eauto.
  Qed.

  Lemma mem_read_bgflush : forall m tid,
      mem_read (mem_bgflush m tid) tid = mem_read m tid.
  Proof.
    destruct m; intros; simpl.
    unfold mem_read; simpl.
    autorewrite with fupd.
    generalize dependent (SBuf0 tid); intros.
    induction l; simpl; auto.
    destruct l; auto.
  Qed.

  Theorem single_value_bgflush : forall m tid v m' tid',
      single_value m tid v ->
      m' = mem_bgflush m tid' ->
      single_value m' tid v.
  Proof.
    unfold single_value; (intuition idtac); subst; simpl.
    destruct (tid' == tid'0); subst;
      autorewrite with fupd.
    rewrite H1 by congruence; auto.
    rewrite H1 by congruence; auto.

    destruct (tid == tid'); subst.
    - apply mem_read_bgflush.
    - unfold mem_bgflush.
      autorewrite with fupd;
        rewrite H1 by congruence.
      rewrite fupd_same by eauto.
      simpl.
      destruct m; simpl; auto.
  Qed.

  Theorem single_value_mem_bg : forall m tid v m',
      single_value m tid v ->
      mem_bg m m' ->
      single_value m' tid v.
  Proof.
    induction 2; repeat deex; eauto using single_value_bgflush.
  Qed.

  Hint Unfold mem_flush : sb.

  Lemma empty_sb_single_value_flush : forall m v tid,
      single_value m tid v ->
      empty_sb (mem_flush m tid).
  Proof.
    autounfold with sb;
      (intuition idtac); subst; simpl.
    destruct (tid == tid0); subst.
    destruct_with_eqn (SBuf m tid0); simpl; eauto.
    autorewrite with fupd; auto.
    destruct_with_eqn (SBuf m tid); simpl; eauto.
    autorewrite with fupd; auto.
  Qed.

  Theorem single_value_mem_flush : forall m tid v m',
      single_value m tid v ->
      m' = mem_flush m tid ->
      single_value m' tid v.
  Proof.
    autounfold with sb;
      (intuition idtac); subst; simpl;
        destruct matches; simpl in *;
          autorewrite with fupd in *;
          eauto.
    simpl_match; auto.
    congruence.
  Qed.

  Lemma single_value_mem_read : forall m tid v,
      single_value m tid v ->
      mem_read m tid = v.
  Proof.
    destruct 1; auto.
  Qed.

End TSOModel.

Arguments mem_bg {T} m1 m2.

Instance mem_bg_PreOrder T : PreOrder (@mem_bg T).
Proof.
  constructor; hnf; intros.
  hnf; constructor.
  eauto using mem_bg_trans.
Defined.
