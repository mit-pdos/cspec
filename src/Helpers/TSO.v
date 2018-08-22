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
  Admitted.

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

  Lemma mem_bgflush_write_commute_nonempty : forall m tid a v,
      m.(SBuf) tid <> [] ->
      mem_write a v (mem_bgflush m tid) tid =
      mem_bgflush (mem_write a v m tid) tid.
  Proof.
  Admitted.

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

  Lemma mem_flush_bgflush_eq : forall m tid,
      mem_flush (mem_bgflush m tid) tid =
      mem_flush m tid.
  Proof.
  Admitted.

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

  Theorem mem_write_single_value : forall m tid a v0 v,
      single_value m tid a v0 ->
      single_value (mem_write a v m tid) tid a v.
  Proof.
  Admitted.

  Lemma mem_read_bgflush : forall a m tid,
      mem_read (mem_bgflush m tid) a tid = mem_read m a tid.
  Proof.
  Admitted.

  Theorem single_value_bgflush : forall m tid a v m' tid',
      single_value m tid a v ->
      m' = mem_bgflush m tid' ->
      single_value m' tid a v.
  Proof.
  Admitted.

  Theorem single_value_mem_bg : forall m tid a v m',
      single_value m tid a v ->
      mem_bg m m' ->
      single_value m' tid a v.
  Proof.
    induction 2; repeat deex; eauto using single_value_bgflush.
  Qed.

  Hint Unfold mem_flush : sb.

  Lemma empty_sb_single_value_flush : forall m a v tid,
      single_value m tid a v ->
      empty_sb (mem_flush m tid).
  Proof.
  Admitted.

  Theorem single_value_mem_flush : forall m tid a v m',
      single_value m tid a v ->
      m' = mem_flush m tid ->
      single_value m' tid a v.
  Proof.
  Admitted.

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
