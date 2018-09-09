Require Import ProofAutomation.
Require Import Helpers.FunMap.
Require Import Helpers.ListStuff.
Require Import Helpers.Instances.
Require Import Relations.Relation_Operators.
Require Import FunctionalExtensionality.

Import List.
Import List.ListNotations.
Open Scope list.

Set Printing Projections.

Section TSOModel.

  Context A {Adec: EqualDec A}.
  Variable T : Type.

  Record memT := mkMem {
    MemValue :> funmap A T;
    SBuf : funmap nat (list (A*T));
  }.

  Fixpoint sbuf_read (ws: list (A*T)) (a:A) (x:T) : T :=
    match ws with
    | nil => x
    | (a', v) :: ws' => if a == a' then v else sbuf_read ws' a x
    end.

  Definition mem_read (m : memT) (a:A) (tid : nat) : T :=
    sbuf_read (m.(SBuf) tid) a (m a).

  Definition mem_write (a:A) (v:T) (m: memT) (tid: nat) : memT :=
    mkMem (MemValue m) (fupd tid ((a,v) :: m.(SBuf) tid) m.(SBuf)).

  Fixpoint sbuf_flush (ws: list (A*T)) (m: funmap A T) : funmap A T :=
    match ws with
    | nil => m
    | (a,v) :: ws' => fupd a v (sbuf_flush ws' m)
    end.

  Definition mem_flush (m : memT) (tid : nat) : memT :=
    mkMem (sbuf_flush (m.(SBuf) tid) m.(MemValue)) (fupd tid nil m.(SBuf)).

  Fixpoint last_error A (l: list A) : option A :=
    match l with
    | [] => None
    | [a] => Some a
    | x::xs => last_error xs
    end.

  Definition mem_bgflush (m : memT) (tid : nat) : memT :=
    match last_error (m.(SBuf) tid) with
    | Some (a, v) => mkMem (fupd a v m.(MemValue)) (fupd tid (removelast (m.(SBuf) tid)) m.(SBuf))
    | None => m
    end.

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

  Lemma mem_bgflush_write_commute_ne : forall a m tid tid' v,
      tid <> tid' ->
      mem_write a v (mem_bgflush m tid) tid' =
      mem_bgflush (mem_write a v m tid') tid.
  Proof.
    intros.
    unfold mem_bgflush, mem_write; simpl.
    autorewrite with fupd.
    destruct_with_eqn (last_error (m.(SBuf) tid)); auto.
    destruct p; simpl; autorewrite with fupd.
    rewrite fupd_fupd_ne by auto; auto.
  Qed.

  Theorem mem_write_flush_same : forall (m:memT) tid a v,
      mem_read m a tid = v ->
      mem_flush (mem_write a v m tid) tid = mem_flush m tid.
  Proof.
    intros.
    unfold mem_read, mem_flush, mem_write in *.
    destruct m; simpl in *.
    apply memT_eq; simpl.
    - generalize dependent (SBuf0 tid); intros ws **.
      generalize dependent v.
      induction ws; simpl; intros.
      + rewrite fupd_eq; simpl.
        rewrite fupd_same; auto.
      + specialize (IHws _ eq_refl).
        rewrite fupd_eq in *; simpl in *.
        destruct a0.
        destruct (a == a0); subst.
        rewrite fupd_fupd_eq by auto; auto.
        rewrite fupd_fupd_ne by auto.
        f_equal; eauto.
    - intros.
      rewrite fupd_fupd_eq; eauto.
  Qed.

  Lemma mem_bgflush_noop : forall m tid,
      m.(SBuf) tid = [] ->
      mem_bgflush m tid = m.
  Proof.
    unfold mem_bgflush; intros.
    rewrite H; simpl.
    apply memT_eq; simpl; intros; auto.
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

  Theorem mem_bgflush_mem_bg_invariant (I: memT -> Prop) :
    (forall m tid, I m -> I (mem_bgflush m tid)) ->
    (forall m m', I m -> mem_bg m m' -> I m').
  Proof.
    intros.
    induction H1; propositional; eauto.
  Qed.

  Theorem mem_flush_empty_sbuf : forall m tid,
      m.(SBuf) tid = [] ->
      mem_flush m tid = m.
  Proof.
    unfold mem_flush; simpl; intros.
    apply memT_eq; simpl; intros.
    rewrite H; auto.
    rewrite fupd_same by auto; auto.
  Qed.

  Theorem mem_bgflush_empty_sbuf : forall m tid,
      m.(SBuf) tid = [] ->
      mem_bgflush m tid = m.
  Proof.
    destruct m.
    unfold mem_bgflush; simpl; intros.
    rewrite H; simpl; auto.
  Qed.

  Theorem last_error_append : forall A (l: list A) a,
      last_error (l ++ [a]) = Some a.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite IHl.
    destruct_with_eqn (l ++ [a0]); eauto.
    destruct l; simpl in *; congruence.
  Qed.

  Lemma removelast_app_one : forall A (l: list A) a,
      removelast (l ++ [a]) = l.
  Proof.
    intros.
    rewrite removelast_app by congruence; simpl.
    rewrite app_nil_r; auto.
  Qed.

  Lemma sbuf_flush_last:
    forall (l : list (A * T)) (a : A) (t : T) (m : memT),
      sbuf_flush (l ++ [(a, t)]) m = sbuf_flush l (fupd a t m).
  Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl.
    rewrite IHl; auto.
  Qed.

  Theorem mem_flush_after_bgflush : forall m tid,
      mem_flush (mem_bgflush m tid) tid = mem_flush m tid.
  Proof.
    intros.
    unfold mem_bgflush.
    remember (m.(SBuf) tid).
    generalize dependent m.
    induction l using rev_ind; simpl; intros.
    - auto.
    - rewrite last_error_append.
      destruct x; simpl.
      rewrite removelast_app_one; simpl.
      unfold mem_flush; simpl.
      autorewrite with fupd.
      f_equal.
      rewrite <- Heql.
      rewrite sbuf_flush_last; auto.
  Qed.

  Theorem mem_bgflush_after_flush : forall m tid,
      mem_bgflush (mem_flush m tid) tid = mem_flush m tid.
  Proof.
    intros.
    unfold mem_flush, mem_bgflush; simpl.
    autorewrite with fupd; simpl; auto.
  Qed.

  Theorem mem_flush_is_mem_bg : forall m tid,
      mem_bg m (mem_flush m tid).
  Proof.
    intros.
    remember (m.(SBuf) tid).
    generalize dependent m.
    induction l using rev_ind; intros.
    - rewrite mem_flush_empty_sbuf by auto.
      constructor.
    - eapply mem_bg_trans with (mem_bgflush m tid).
      econstructor; [ eauto | constructor ].

      replace (mem_flush m tid) with (mem_flush (mem_bgflush m tid) tid).
      { apply IHl.
        unfold mem_bgflush.
        rewrite <- Heql.
        rewrite last_error_append.
        destruct x; simpl.
        rewrite removelast_app by congruence; simpl; rewrite app_nil_r.
        autorewrite with fupd; auto. }
      rewrite mem_flush_after_bgflush; auto.
  Qed.

  Theorem mem_bgflush_mem_flush_invariant (I: memT -> Prop) :
    (forall m tid, I m -> I (mem_bgflush m tid)) ->
    (forall m tid, I m -> I (mem_flush m tid)).
  Proof.
    intros.
    eapply mem_bgflush_mem_bg_invariant; eauto.
    apply mem_flush_is_mem_bg.
  Qed.

  Definition list_last_dec X (l: list X) : {l = []} + {exists l' a, l = l' ++ [a]}.
    destruct l; eauto.
    right.
    induction l using rev_ind; simpl; propositional.
    exists nil; simpl; eauto.
    rewrite app_comm_cons.
    rewrite H; eauto.
  Qed.

  Lemma mem_bgflush_write_commute_nonempty : forall m tid a v,
      m.(SBuf) tid <> [] ->
      mem_write a v (mem_bgflush m tid) tid =
      mem_bgflush (mem_write a v m tid) tid.
  Proof.
    unfold mem_write, mem_bgflush; simpl; intros.
    destruct (list_last_dec (m.(SBuf) tid)); propositional; try congruence.
    rewrite H0.
    rewrite last_error_append, removelast_app_one.
    destruct a0; simpl; autorewrite with fupd.
    rewrite app_comm_cons.
    rewrite last_error_append, removelast_app_one.
    auto.
  Qed.

  Lemma mem_bg_commute_write : forall m1 m2 m3 m4 a v tid,
      mem_bg m1 m2 ->
      m3 = mem_write a v m2 tid ->
      mem_bg m3 m4 ->
      mem_bg (mem_write a v m1 tid) m4.
  Proof.
    intros; subst.
    eapply mem_bg_transform_commute with
        (f := fun m => mem_write a v m tid);
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

  Lemma sbuf_flush_read_comm:
    forall f a (l : list (A * T)),
      sbuf_flush l f a = sbuf_read l a (f a).
  Proof.
    induction l; simpl; auto.
    destruct a0.
    destruct (a == a0); subst; autorewrite with fupd; auto.
  Qed.

  Lemma sbuf_read_one_more:
    forall (m : memT) (a : A) (l : list (A * T)) (a0 : A) (t : T),
      sbuf_read l a (fupd a0 t m a) = sbuf_read (l ++ [(a0, t)]) a (m a).
  Proof.
    induction l; simpl; intros.
    destruct (a == a0); subst; autorewrite with fupd; eauto.
    destruct a0.
    destruct (a == a0); subst; autorewrite with fupd; eauto.
  Qed.

  Lemma mem_read_mem_bgflush_eq : forall m a tid,
      mem_read (mem_bgflush m tid) a tid = mem_read m a tid.
  Proof.
    intros.
    unfold mem_read, mem_bgflush; simpl; intros.
    destruct (list_last_dec (m.(SBuf) tid)); propositional; auto.
    - rewrite e; simpl; auto.
      rewrite e; simpl; auto.
    - rewrite H.
      rewrite last_error_append, removelast_app_one.
      destruct a0; simpl; autorewrite with fupd.
      rewrite sbuf_read_one_more; auto.
  Qed.

  Lemma mem_read_mem_flush_eq : forall m a tid,
      mem_read (mem_flush m tid) a tid = mem_read m a tid.
  Proof.
    intros.
    unfold mem_read, mem_flush; simpl; intros.
    autorewrite with fupd; simpl.
    rewrite sbuf_flush_read_comm; auto.
  Qed.

  Lemma mem_read_mem_write_ne : forall m a a' v' tid,
      a <> a' ->
      mem_read (mem_write a' v' m tid) a tid = mem_read m a tid.
  Proof.
    unfold mem_read, mem_write; simpl; intros.
    autorewrite with fupd; simpl.
    destruct (a == a'); subst; congruence.
  Qed.

  Lemma mem_read_mem_write_eq : forall m a v' tid,
      mem_read (mem_write a v' m tid) a tid = v'.
  Proof.
    unfold mem_read, mem_write; simpl; intros.
    autorewrite with fupd; simpl.
    destruct (a == a); subst; congruence.
  Qed.

  Definition empty_sb (m:memT) := forall tid, m.(SBuf) tid = [].

  Theorem empty_sb_mem_bgflush_noop : forall m tid,
      empty_sb m ->
      mem_bgflush m tid = m.
  Proof.
    unfold empty_sb, mem_bgflush; intros.
    apply memT_eq; simpl; intros.
    rewrite H; auto.
    rewrite H; simpl.
    auto.
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
    rewrite fupd_same; auto.
  Qed.

  Theorem empty_sb_mem_read : forall m a tid,
      empty_sb m ->
      mem_read m a tid = m.(MemValue) a.
  Proof.
    unfold empty_sb, mem_read; intros.
    rewrite H; auto.
  Qed.

  Definition single_value (m:memT) tid a v :=
    (forall tid', tid <> tid' -> m.(SBuf) tid' = []) /\
    mem_read m a tid = v.

  Hint Unfold empty_sb single_value
       mem_read mem_write mem_bgflush : sb.

  Theorem empty_sb_single_value : forall m a,
      empty_sb m ->
      forall tid, single_value m tid a (m.(MemValue) a).
  Proof.
    autounfold with sb; simpl; intuition eauto.
    rewrite H; auto.
  Qed.

  Hint Unfold mem_flush : sb.

  Lemma single_value_mem_read : forall m tid a v,
      single_value m tid a v ->
      mem_read m a tid = v.
  Proof.
    destruct 1; auto.
  Qed.

End TSOModel.

Arguments mem_bg {A Adec T} m1 m2.

Instance mem_bg_PreOrder A {_:EqualDec A} T : PreOrder (mem_bg (A:=A) (T:=T)).
Proof.
  constructor; hnf; intros.
  hnf; constructor.
  eauto using mem_bg_trans.
Defined.
