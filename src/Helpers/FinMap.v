(* representation of thread states as a a finite partial map, with an explicit
bound beyond which no more threads are mapped *)

Require Import Arith.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import ProofAutomation.
Require Import Helpers.Instances.

Require Import ConcurProc.

Set Implicit Arguments.

Section Map.
  Notation A := nat.

  Variable Op : Type -> Type.
  Notation V := (maybe_proc Op).

  Local Record threads_state :=
    { thread_get :> A -> V;
      thread_max : nat;
      mapping_finite : forall a, thread_max < a -> thread_get a = NoProc;
      thread_max_minimal : (thread_get thread_max <> NoProc) \/ thread_max = 0 }.

  Notation t := threads_state.

  Hint Extern 4 (_ < _) => omega.
  Hint Resolve mapping_finite.
  Hint Extern 2 (_ <> _) => congruence.
  Hint Extern 2 (_ = _ -> False) => congruence.
  Hint Resolve thread_max_minimal.

  Fixpoint lower_mapping (x:threads_state) n : A :=
    match n with
    | 0 => 0
    | S n' => match x n' with
             | Proc _ => n'
             | NoProc => lower_mapping x n'
             end
    end.

  Theorem lower_mapping_smaller : forall x n,
      lower_mapping x n < n \/ n = 0.
  Proof.
    induction n; simpl; auto.
    destruct (x n); intuition auto.
    subst; auto.
  Qed.

  Theorem lower_mapping_not_none : forall (x:t) n,
      x (lower_mapping x n) <> NoProc \/
      lower_mapping x n = 0.
  Proof.
    induction n; simpl; auto.
    destruct_with_eqn (x n); intuition auto.
  Qed.

  Theorem lower_mapping_thread_maximal : forall x n,
      forall a, lower_mapping x n < a -> a < n -> x a = NoProc.
  Proof.
    intros.
    induction n; simpl in *; intros.
    exfalso; omega.
    destruct_with_eqn (x n); auto.
    destruct (a == n); subst; auto.
  Qed.

  Definition thread_upd (x:t) (a:A) (v:V) : t.
    refine {| thread_get :=
                fun a' => if a == a' then v else x a';
              thread_max :=
                if lt_dec (thread_max x) a then
                  (* modification past current end *)
                  match v with
                  | Proc _ => a
                  | NoProc => thread_max x (* no-op *)
                  end else
                  match v with
                  | Proc _ => thread_max x
                  | NoProc => (* deleting from the middle; might need to lower thread_max *)
                    if a == thread_max x then
                      lower_mapping x (thread_max x) else
                      thread_max x
                  end|};
      intros.
    - destruct (lt_dec (thread_max x) a), (a == a0), v; subst; try omega; auto.
      destruct (a == thread_max x); subst; auto.
      destruct (lt_dec a0 (thread_max x)); auto.
      apply lower_mapping_thread_maximal with (n := thread_max x); auto.
    - destruct (lt_dec (thread_max x) a), v; subst;
        repeat match goal with
               | |- context[if ?a == ?b then _ else _] => destruct (a == b)
               end; subst; try omega; auto.
      destruct (lower_mapping_smaller x (thread_max x)); try omega.
      rewrite H; simpl; auto.
      destruct (lower_mapping_not_none x (thread_max x)); auto.
  Defined.

  Theorem thread_ext_eq : forall (x y:t),
      (forall tid, x tid = y tid) ->
      x = y.
  Proof.
    intros.
    destruct x as [x x_thread_max mapping_finite_x thread_max_minimal_x].
    destruct y as [y y_thread_max mapping_finite_y thread_max_minimal_y].
    simpl in *.
    assert (x = y).
    extensionality tid; auto.
    subst y.
    clear H.
    assert (x_thread_max = y_thread_max). { (* the main proof *)
      destruct thread_max_minimal_x, thread_max_minimal_y; subst; auto.
      - assert (~x_thread_max < y_thread_max) by (intro; eauto).
        assert (~y_thread_max < x_thread_max) by (intro; eauto).
        omega.
      - specialize (mapping_finite_y x_thread_max).
        destruct x_thread_max; auto.
        exfalso; auto.
      - specialize (mapping_finite_x y_thread_max).
        destruct y_thread_max; auto.
        exfalso; auto.
    }
    subst.
    f_equal; auto using proof_irrelevance.
  Qed.

  Ltac t :=
    intros;
    try lazymatch goal with
        | |- @eq t _ _ => apply thread_ext_eq; intros
        end;
    simpl;
    repeat match goal with
           | [ |- context[?a == ?a' ] ] =>
             destruct (a == a')
           | _ => congruence
           end.

  Theorem thread_upd_eq : forall x a v,
      thread_upd x a v a = v.
  Proof.
    t.
  Qed.

  Theorem thread_upd_ne: forall (x:t) a a' v,
      a <> a' ->
      thread_upd x a v a' = x a'.
  Proof.
    t.
  Qed.

  Theorem thread_upd_thread_upd_eq : forall x a v v',
      thread_upd (thread_upd x a v) a v' = thread_upd x a v'.
  Proof.
    t.
  Qed.

  Theorem thread_upd_ne_comm : forall (ts:t) tid tid' p p',
      tid <> tid' ->
      thread_upd (thread_upd ts tid p) tid' p' =
      thread_upd (thread_upd ts tid' p') tid p.
  Proof.
    t.
  Qed.

  Theorem thread_upd_same_eq : forall (ts:t) tid p,
      ts tid = p ->
      thread_upd ts tid p = ts.
  Proof.
    t.
  Qed.

  Theorem thread_upd_thread_max_bound : forall (x:t) a v,
      a <= thread_max x ->
      thread_max (thread_upd x a v) <= thread_max x.
  Proof.
    simpl; intros.
    generalize dependent (thread_max x); intros m **.
    destruct (lt_dec m a).
    destruct v; auto.
    destruct v; auto.
    destruct (a == m); subst; auto.
    destruct (lower_mapping_smaller x m); subst; auto.
    omega.
  Qed.

  Theorem thread_upd_thread_max_extend : forall (x:t) a T v,
      a > thread_max x ->
      thread_max (thread_upd x a (Proc (T:=T) v)) > thread_max x.
  Proof.
    simpl; intros.
    generalize dependent (thread_max x); intros m **.
    destruct (lt_dec m a); auto.
  Qed.

  Theorem thread_upd_thread_max_extend_bound : forall (x:t) a v,
      a >= thread_max x ->
      thread_max (thread_upd x a v) <= a.
  Proof.
    simpl; intros.
    generalize dependent (thread_max x); intros m **.
    destruct (lt_dec m a); auto.
    destruct v; auto; try omega.
    destruct v; auto; try omega.
    destruct (a == m); subst; auto.
    destruct (lower_mapping_smaller x m); subst; auto.
    omega.
  Qed.

  Theorem thread_upd_thread_max_shrink : forall (x:t) a,
      thread_max (thread_upd x a NoProc) <= thread_max x.
  Proof.
    simpl; intros.
    generalize dependent (thread_max x); intros m **.
    destruct (lt_dec m a); auto.
    destruct (a == m); subst; auto.
    destruct (lower_mapping_smaller x m); subst; auto.
    omega.
  Qed.

  Theorem thread_upd_unchanged : forall (x:t) a T (v: proc Op T),
      a <= thread_max x ->
      thread_max (thread_upd x a (Proc v)) = thread_max x.
  Proof.
  Abort.

  Theorem past_thread_max_empty : forall (x:t),
      x (1 + thread_max x) = NoProc.
  Proof.
    intros.
    apply mapping_finite; omega.
  Qed.

  Definition thread_empty : t.
    refine {| thread_get := fun _ => NoProc;
              thread_max := 0; |}; auto.
  Defined.

  Theorem empty_is_empty : forall a,
      thread_empty a = NoProc.
  Proof.
    simpl; auto.
  Qed.

  Theorem thread_empty_not_some : forall a T (v: proc Op T),
      ~thread_empty a = Proc v.
  Proof.
    simpl; auto.
  Qed.

  Theorem thread_empty_unique : forall (x:t),
      (forall a, x a = NoProc) ->
      x = thread_empty.
  Proof.
    t.
  Qed.

  Theorem empty_thread_max :
    thread_max thread_empty = 0.
  Proof.
    t.
  Qed.

  Definition thread_Forall (P: forall T, proc Op T -> Prop) (ts:t) :=
    forall tid T (p: proc Op T), ts tid = Proc p -> P _ p.

  Theorem thread_Forall_some : forall P x a T (v: proc Op T),
      thread_Forall P x ->
      x a = Proc v ->
      P _ v.
  Proof.
    unfold thread_Forall; eauto.
  Qed.

  Theorem empty_thread_Forall : forall P,
      thread_Forall P thread_empty.
  Proof.
    unfold thread_Forall; intros.
    apply thread_empty_not_some in H; contradiction.
  Qed.

  Theorem thread_Forall_thread_upd_some : forall P ts tid T (p: proc Op T),
      thread_Forall P ts ->
      P _ p ->
      thread_Forall P (thread_upd ts tid (Proc p)).
  Proof.
    unfold thread_Forall.
    t.
    destruct (tid == tid0); subst;
      rewrite ?Map.thread_upd_eq, ?Map.thread_upd_ne in * by auto;
      subst;
      eauto.
    invert H1.
  Qed.

  Theorem thread_Forall_forall : forall (P: forall T, proc Op T -> Prop) (x:t),
      (forall a T (v: proc _ T), x a = Proc v -> P _ v) ->
      thread_Forall P x.
  Proof.
    unfold thread_Forall; eauto.
  Qed.

  Theorem thread_Forall_thread_upd_none : forall P x tid,
      thread_Forall P x ->
      thread_Forall P (thread_upd x tid NoProc).
  Proof.
    unfold thread_Forall.
    t.
    destruct (tid == tid0); subst;
      rewrite ?Map.thread_upd_eq, ?Map.thread_upd_ne in * by auto;
      subst;
      eauto.
    congruence.
  Qed.

  Definition thread_from_list (l: list {T & proc Op T}) : t.
    refine {| thread_get := fun a => match List.nth_error l a with
                                  | Some (existT _ _ p) => Proc p
                                  | None => NoProc
                                  end;
              thread_max := length l - 1; |}.
    intros.
    assert (length l <= a) by omega.
    apply List.nth_error_None in H0.
    simpl_match; auto.
    destruct_with_eqn (List.nth_error l (length l - 1)); eauto.
    destruct s; left; congruence.
    right.
    apply List.nth_error_None in Heqo.
    omega.
  Defined.

  Local Fixpoint _to_list (x:t) n : list V :=
    match n with
    | 0 => nil
    | S n' => _to_list x n' ++ (x n'::nil)
    end.

  Definition thread_to_list (x:t) : list V := _to_list x (1 + thread_max x).

  Lemma firstn_map : forall A B (f: A -> B) n (l: list A),
      List.firstn n (List.map f l) = List.map f (List.firstn n l).
  Proof.
    induction n; simpl; intros; auto.
    destruct l; simpl; eauto.
    rewrite IHn; auto.
  Qed.

  Lemma nth_error_nil : forall A n,
      List.nth_error (@nil A) n = None.
  Proof.
    induction n; simpl; eauto.
  Qed.

  (* TODO: prove this, just for fun (note that it is unused; conversion back
    to lists is only for extraction purposes) *)
  Lemma from_list__to_list : forall l n,
      n <= length l ->
      _to_list (thread_from_list l) n = List.firstn n (List.map (fun '(existT _ _ p) => Proc p) l).
  Proof.
    induction n; intros; auto.
    cbn [_to_list thread_get thread_from_list].
    rewrite IHn by omega.
    rewrite ?firstn_map.
    clear IHn.
    fold (lt n (length l)) in H.
  Admitted.

  Theorem thread_from_list_to_list : forall l,
      0 < length l ->
      thread_to_list (thread_from_list l) = List.map (fun '(existT _ _ p) => Proc p) l.
  Proof.
    unfold thread_to_list; intros.
    unfold thread_to_list.
    rewrite from_list__to_list by (simpl; omega).
    rewrite List.firstn_all2; auto.
    rewrite List.map_length.
    simpl; omega.
  Qed.

End Map.

Theorem thread_max_eq : forall Op1 Op2 (ts1:threads_state Op1) (ts2:threads_state Op2),
    (forall tid, ts1 tid = NoProc <-> ts2 tid = NoProc) ->
    thread_max ts1 = thread_max ts2.
Proof.
  (* will do proof by symmetry *)
  assert (forall V1 V2 (x1:threads_state V1) (x2:threads_state V2),
             (forall a, x1 a = NoProc <-> x2 a = NoProc) ->
             thread_max x1 < thread_max x2 -> False).
  intros.
  pose proof (@mapping_finite _ x1 (thread_max x2) ltac:(omega)).
  apply H in H1.
  destruct (thread_max_minimal x2); try congruence.
  omega.

  intros.
  assert (forall a, ts2 a = NoProc <-> ts1 a = NoProc).
  split; intuition auto.
  apply H0; auto.
  apply H0; auto.
  pose proof (H _ _ ts1 ts2).
  pose proof (H _ _ ts2 ts1).
  intuition auto.
  omega.
Qed.

Section Map_map.

  Variable Op1:Type -> Type.
  Variable Op2:Type -> Type.
  Variable f:forall T, proc Op1 T -> proc Op2 T.

  Definition thread_map (x:threads_state Op1) : threads_state Op2.
    refine {| thread_get := fun a => match x a with
                                  | NoProc => NoProc
                                  | Proc v => Proc (f v)
                                  end;
              thread_max := thread_max x; |}; intros.
    destruct_with_eqn (x a); eauto.
    rewrite mapping_finite in Heqm by auto; congruence.

    destruct (thread_max_minimal x); auto.
    destruct (x (thread_max x)); auto.
    left; congruence.
  Defined.

  Theorem thread_map_get_match : forall (x:threads_state Op1) a,
      thread_map x a = match x a with
                       | Proc v => Proc (f v)
                       | NoProc => NoProc
                       end.
  Proof.
    simpl; auto.
  Qed.

  Theorem map_thread_get_some : forall (x:threads_state Op1) a T (v: proc Op1 T),
      x a = Proc v ->
      thread_map x a = Proc (f v).
  Proof.
    simpl; intros.
    rewrite H; auto.
  Qed.

  Theorem map_thread_get_none : forall (x:threads_state Op1) a,
      x a = NoProc ->
      thread_map x a = NoProc.
  Proof.
    simpl; intros.
    rewrite H; auto.
  Qed.

  Theorem map_thread_Forall : forall (P: forall T, proc Op1 T -> Prop) (Q:forall T, proc Op2 T -> Prop) (x:threads_state Op1),
      thread_Forall P x ->
      (forall T v, P T v -> Q T (f v)) ->
      thread_Forall Q (thread_map x).
  Proof.
    unfold thread_Forall; simpl; intros.
    destruct_with_eqn (x tid).
    inversion H1; subst; eauto.
    congruence.
  Qed.

End Map_map.

Global Opaque
       thread_get
       thread_upd
       thread_empty
       thread_Forall
       thread_from_list
       thread_to_list
       thread_map.

Arguments thread_empty {Op}.

Hint Rewrite thread_upd_eq : t.
Hint Rewrite thread_upd_ne using solve [ auto ] : t.
Hint Rewrite thread_upd_thread_upd_eq : t.
Hint Rewrite thread_upd_same_eq using solve [ auto ] : t.
Hint Rewrite map_thread_get_none using solve [ auto ] : t.
Hint Rewrite empty_thread_max : t.
