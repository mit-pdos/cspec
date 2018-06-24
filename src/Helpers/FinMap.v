(* a finite partial map *)

Require Import Arith.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Set Implicit Arguments.

Module Map.
  Section Map.
    Notation A := nat.
    Infix "==" := Nat.eq_dec (no associativity, at level 30).

    Variable V:Type.

    Local Record t :=
      { get :> A -> option V;
        max : nat;
        mapping_finite : forall a, max < a -> get a = None;
        max_minimal : (get max <> None) \/ max = 0 }.

    Hint Extern 4 (_ < _) => omega.
    Hint Resolve mapping_finite.
    Hint Extern 2 (_ <> _) => congruence.
    Hint Extern 2 (_ = _ -> False) => congruence.
    Hint Resolve max_minimal.

    Fixpoint lower_mapping (x:t) n : A :=
      match n with
      | 0 => 0
      | S n' => match x n' with
               | Some _ => n'
               | None => lower_mapping x n'
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
        x (lower_mapping x n) <> None \/
        lower_mapping x n = 0.
    Proof.
      induction n; simpl; auto.
      destruct_with_eqn (x n); intuition auto.
    Qed.

    Theorem lower_mapping_maximal : forall x n,
        forall a, lower_mapping x n < a -> a < n -> x a = None.
    Proof.
      intros.
      induction n; simpl in *; intros.
      exfalso; omega.
      destruct_with_eqn (x n); auto.
      destruct (a == n); subst; auto.
    Qed.

    Definition upd (x:t) (a:A) (v:option V) : t.
      refine {| get :=
                  fun a' => if a == a' then v else x a';
                max :=
                  if lt_dec (max x) a then
                    (* modification past current end *)
                    match v with
                    | Some _ => a
                    | None => max x (* no-op *)
                    end else
                    match v with
                    | Some _ => max x
                    | None => (* deleting from the middle; might need to lower max *)
                        if a == max x then
                          lower_mapping x (max x) else
                          max x
                    end|};
        intros.
      - destruct (lt_dec (max x) a), (a == a0), v; subst; try omega; auto.
        destruct (a == max x); subst; auto.
        destruct (lt_dec a0 (max x)); auto.
        apply lower_mapping_maximal with (n := max x); auto.
      - destruct (lt_dec (max x) a), v; subst;
          repeat match goal with
                 | |- context[if ?a == ?b then _ else _] => destruct (a == b)
                 end; subst; try omega; auto.
        destruct (lower_mapping_smaller x (max x)); try omega.
        rewrite H; simpl; auto.
        destruct (lower_mapping_not_none x (max x)); auto.
    Defined.

    Theorem t_ext_eq : forall (x y:t),
        (forall a, x a = y a) ->
        x = y.
    Proof.
      intros.
      destruct x as [x x_max mapping_finite_x max_minimal_x].
      destruct y as [y y_max mapping_finite_y max_minimal_y].
      simpl in *.
      assert (x = y).
      extensionality a; auto.
      subst y.
      clear H.
      assert (x_max = y_max). { (* the main proof *)
        destruct max_minimal_x, max_minimal_y; subst; auto.
        - assert (~x_max < y_max) by (intro; eauto).
          assert (~y_max < x_max) by (intro; eauto).
          omega.
        - specialize (mapping_finite_y x_max).
          destruct x_max; auto.
          exfalso; auto.
        - specialize (mapping_finite_x y_max).
          destruct y_max; auto.
          exfalso; auto.
      }
      subst.
      f_equal; auto using proof_irrelevance.
    Qed.

    Ltac t :=
      intros;
      try lazymatch goal with
          | |- @eq t _ _ => apply t_ext_eq; intros
          end;
      simpl;
      repeat match goal with
             | [ |- context[?a == ?a' ] ] =>
               destruct (a == a')
             | _ => congruence
             end.

    Theorem upd_eq : forall x a v,
        upd x a v a = v.
    Proof.
      t.
    Qed.

    Theorem upd_ne: forall (x:t) a a' v,
        a <> a' ->
        upd x a v a' = x a'.
    Proof.
      t.
    Qed.

    Theorem upd_upd_eq : forall x a v v',
        upd (upd x a v) a v' = upd x a v'.
    Proof.
      t.
    Qed.

    Theorem upd_ne_comm : forall (x:t) a a' v v',
        a <> a' ->
        upd (upd x a v) a' v' = upd (upd x a' v') a v.
    Proof.
      t.
    Qed.

    Theorem upd_same_eq : forall (x:t) a v,
        x a = v ->
        upd x a v = x.
    Proof.
      t.
    Qed.

    Theorem upd_max_bound : forall (x:t) a v,
        a <= max x ->
        max (upd x a v) <= max x.
    Proof.
      simpl; intros.
      generalize dependent (max x); intros m **.
      destruct (lt_dec m a).
      destruct v; auto.
      destruct v; auto.
      destruct (a == m); subst; auto.
      destruct (lower_mapping_smaller x m); subst; auto.
      omega.
    Qed.

    Theorem upd_max_extend : forall (x:t) a v,
        a > max x ->
        max (upd x a (Some v)) > max x.
    Proof.
      simpl; intros.
      generalize dependent (max x); intros m **.
      destruct (lt_dec m a); auto.
    Qed.

    Theorem upd_max_extend_bound : forall (x:t) a v,
        a >= max x ->
        max (upd x a v) <= a.
    Proof.
      simpl; intros.
      generalize dependent (max x); intros m **.
      destruct (lt_dec m a); auto.
      destruct v; auto; try omega.
      destruct v; auto; try omega.
      destruct (a == m); subst; auto.
      destruct (lower_mapping_smaller x m); subst; auto.
      omega.
    Qed.

    Theorem upd_max_shrink : forall (x:t) a,
        max (upd x a None) <= max x.
    Proof.
      simpl; intros.
      generalize dependent (max x); intros m **.
      destruct (lt_dec m a); auto.
      destruct (a == m); subst; auto.
      destruct (lower_mapping_smaller x m); subst; auto.
      omega.
    Qed.

    Theorem upd_unchanged : forall (x:t) a v,
        a <= max x ->
        max (upd x a (Some v)) = max x.
    Proof.
    Abort.

    Theorem past_max_empty : forall (x:t),
        x (1 + max x) = None.
    Proof.
      intros.
      apply mapping_finite; omega.
    Qed.

    Definition empty : t.
      refine {| get := fun _ => None;
                max := 0; |}; auto.
    Defined.

    Theorem empty_is_empty : forall a,
        empty a = None.
    Proof.
      simpl; auto.
    Qed.

    Theorem empty_not_some : forall a v,
        ~empty a = Some v.
    Proof.
      simpl; auto.
    Qed.

    Theorem empty_unique : forall (x:t),
        (forall a, x a = None) ->
        x = empty.
    Proof.
      t.
    Qed.

    Theorem empty_max :
      max empty = 0.
    Proof.
      t.
    Qed.

    Definition Forall (P: V -> Prop) (x:t) :=
      forall a v, x a = Some v -> P v.

    Theorem Forall_some : forall P x a v,
        Forall P x ->
        x a = Some v ->
        P v.
    Proof.
      unfold Forall; eauto.
    Qed.

    Theorem empty_Forall : forall P,
        Forall P empty.
    Proof.
      unfold Forall; intros.
      apply empty_not_some in H; contradiction.
    Qed.

    Theorem Forall_upd_some : forall P x a v,
        Forall P x ->
        P v ->
        Forall P (upd x a (Some v)).
    Proof.
      unfold Forall.
      t.
      destruct (a == a0); subst;
        rewrite ?Map.upd_eq, ?Map.upd_ne in * by auto;
        subst;
        eauto.
      congruence.
    Qed.

    Theorem Forall_forall : forall (P: V -> Prop) (x:t),
        (forall a v, x a = Some v -> P v) ->
        Forall P x.
    Proof.
      unfold Forall; eauto.
    Qed.

    Theorem Forall_upd_none : forall P x a,
        Forall P x ->
        Forall P (upd x a None).
    Proof.
      unfold Forall.
      t.
      destruct (a == a0); subst;
        rewrite ?Map.upd_eq, ?Map.upd_ne in * by auto;
        subst;
        eauto.
      congruence.
    Qed.

    Definition from_list (l: list V) : t.
      refine {| get := fun a => List.nth_error l a;
                max := length l - 1; |}.
      intros.
      apply List.nth_error_None; omega.
      destruct_with_eqn (List.nth_error l (length l - 1)); eauto.
      right.
      apply List.nth_error_None in Heqo.
      omega.
    Defined.

    Theorem from_list_get : forall l a,
        from_list l a = List.nth_error l a.
    Proof.
      auto.
    Qed.

    Local Fixpoint _to_list (x:t) n : list (option V) :=
      match n with
      | 0 => nil
      | S n' => _to_list x n' ++ (x n'::nil)
      end.

    Definition to_list (x:t) : list (option V) := _to_list x (1 + max x).

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
        _to_list (from_list l) n = List.firstn n (List.map Some l).
    Proof.
      induction n; intros; auto.
      cbn [_to_list get from_list].
      rewrite IHn by omega.
      rewrite ?firstn_map.
      clear IHn.
      fold (lt n (length l)) in H.
    Admitted.

    Theorem from_list_to_list : forall l,
        0 < length l ->
        to_list (from_list l) = List.map Some l.
    Proof.
      unfold to_list; intros.
      unfold to_list.
      rewrite from_list__to_list by (simpl; omega).
      rewrite List.firstn_all2; auto.
      rewrite List.map_length.
      simpl; omega.
    Qed.

  End Map.

  Theorem max_eq : forall V1 V2 (x1:t V1) (x2:t V2),
      (forall a, x1 a = None <-> x2 a = None) ->
      max x1 = max x2.
  Proof.
    (* will do proof by symmetry *)
    assert (forall V1 V2 (x1:t V1) (x2:t V2),
               (forall a, x1 a = None <-> x2 a = None) ->
               max x1 < max x2 -> False).
    intros.
    pose proof (@mapping_finite _ x1 (max x2) ltac:(omega)).
    apply H in H1.
    destruct (max_minimal x2); try congruence.
    omega.

    intros.
    assert (forall a, x2 a = None <-> x1 a = None).
    split; intuition auto.
    apply H0; auto.
    apply H0; auto.
    pose proof (H _ _ x1 x2).
    pose proof (H _ _ x2 x1).
    intuition auto.
    omega.
  Qed.

  Section Map_map.

    Variable V1:Type.
    Variable V2:Type.
    Variable f:V1 -> V2.

    Definition map (x:t V1) : t V2.
      refine {| get := fun a => match x a with
                             | None => None
                             | Some v => Some (f v)
                             end;
                max := max x; |}; intros.
      destruct_with_eqn (x a); eauto.
      rewrite mapping_finite in Heqo by auto; congruence.

      destruct (max_minimal x); auto.
      destruct (x (max x)); auto.
      left; congruence.
    Defined.

    Theorem map_get_match : forall (x:t V1) a,
        map x a = match x a with
                  | Some v => Some (f v)
                  | None => None
                  end.
    Proof.
      simpl; auto.
    Qed.

    Theorem map_get_some : forall (x:t V1) a v,
        x a = Some v ->
        map x a = Some (f v).
    Proof.
      simpl; intros.
      rewrite H; auto.
    Qed.

    Theorem map_get_none : forall (x:t V1) a,
        x a = None ->
        map x a = None.
    Proof.
      simpl; intros.
      rewrite H; auto.
    Qed.

    Theorem map_Forall : forall (P: V1 -> Prop) (Q:V2 -> Prop) (x:t V1),
        Forall P x ->
        (forall v, P v -> Q (f v)) ->
        Forall Q (map x).
    Proof.
      unfold Forall; simpl; intros.
      destruct_with_eqn (x a).
      inversion H1; subst; eauto.
      congruence.
    Qed.

  End Map_map.

End Map.

Global Opaque Map.get Map.upd Map.empty Map.Forall Map.from_list Map.map.

Hint Rewrite Map.upd_eq : upd.
Hint Rewrite Map.upd_ne using solve [ auto ] : upd.
Hint Rewrite Map.upd_upd_eq : upd.
Hint Rewrite Map.upd_same_eq using solve [ auto ] : upd.
Hint Rewrite Map.map_get_none using solve [ auto ] : upd.
Hint Rewrite Map.empty_max : upd.
