Require Import Omega.

Require Import Automation.
Require Import Pocs.Ensemble.
Require Import Disk.AsyncDisk.

Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import
        TwoDisk.AsyncTwoDiskAPI
        TwoDisk.AsyncTwoDiskTheorems
        TwoDisk.TwoDiskFacts.

Require Import
        SeqDisk.AsyncReplicatedDisk.Step
        SeqDisk.AsyncReplicatedDisk.DiskSize.

Require Import MaybeHolds.

Section AsyncReplicatedDisk.

    Variable (td:Interface TD.API).

    (* Recovery tracks what happens at each step in order to implement control
       flow. *)
    Inductive RecStatus :=
    (* continue working, nothing interesting has happened *)
    | Continue
    (* one of the disks has failed, so don't bother continuing recovery since the
       invariant is now trivially satisfied *)
    | DiskFailed (i:diskId).

    Definition fixup (a:addr) : prog RecStatus :=
      mv0 <- Prim td (TD.Read d0 a);
        match mv0 with
        | Working v => mv2 <- Prim td (TD.Read d1 a);
                        match mv2 with
                        | Working v' => if v == v' then
                                         Ret Continue
                                       else
                                         mu <- Prim td (TD.Write d1 a v);
                                         Ret (match mu with
                                              | Working _ => Continue
                                              | Failed => DiskFailed d1
                                              end)
                        | Failed => Ret (DiskFailed d1)
                        end
        | Failed => Ret (DiskFailed d0)
        end.

    (* recursively performs recovery at [a-1], [a-2], down to 0 *)
    Fixpoint recover_at (a:addr) : prog RecStatus :=
      match a with
      | 0 => Ret Continue
      | S n => s <- fixup n;
                match s with
                | Continue => recover_at n
                | DiskFailed i => Ret (DiskFailed i)
                end
      end.

    Definition Recover : prog unit :=
      sz <- DiskSize td;
        _ <- recover_at sz;
        _ <- Prim td (TD.Sync d1);
        Ret tt.

    Record equal_after (a:addr) (d_0 d_1:histdisk) : Prop :=
      { equal_after_sizes_eq : size d_0 = size d_1;
        equal_after_holds : forall a', a <= a' ->
                                  match d_0 a', d_1 a' with
                                  | Some b0, Some b1 => curr_val b0 = curr_val b1
                                  | None, None => True
                                  | _, _ => False
                                  end; }.

    (* crashesTo_one_of d_0 d_1 d says [forall a, d_0(a) ~> d(a) \/ d_1(a) ~> d(a)]
    where [h ~> h'] is made-up notation for h crashing to the current value in
    h' (with h also having durable values from the union of d_0(a) and d_1(a)).

     This isn't a pointwise_rel, unfortunately, since it covers three disks. *)
    Record crashesTo_one_of' (d_0 d_1 d:histdisk) : Prop :=
      { crashesTo_one'_size0 : size d_0 = size d;
        crashesTo_one'_size1 : size d_1 = size d;
        crashesTo_one'_pointwise : forall a,
            match d_0 a, d_1 a, d a with
            | Some h0, Some h1, Some h => (In (curr_val h) (durable_vals h0) \/
                                          In (curr_val h) (durable_vals h1)) /\
                                         contains (durable_vals h)
                                                  (Union (durable_vals h0)
                                                         (durable_vals h1))
            | None, None, None => True
            | _, _, _ => False
            end;
      }.

    Hint Resolve pred_weaken.

    Lemma equal_after_already_eq : forall a (d_0 d_1:histdisk) v,
        a < size d_0 ->
        d_0 a |= curr_val_eq v ->
        d_1 a |= curr_val_eq v ->
        equal_after (S a) d_0 d_1 ->
        equal_after a d_0 d_1.
    Proof.
      intros.
      destruct H2.
      econstructor; intros; eauto.
      apply Lt.le_lt_or_eq in H2; intuition subst.
      eapply equal_after_holds0.
      omega.
      destruct matches; simpl in *;
        eauto using same_size_disks_not_different.
    Qed.

    Hint Resolve equal_after_already_eq.

    Lemma equal_after_upd : forall a (d_0 d_1:histdisk) v,
        d_0 a |= curr_val_eq v ->
        equal_after (S a) d_0 d_1 ->
        equal_after a d_0 (diskUpdF d_1 a (buffer v)).
    Proof.
      intros.
      destruct H0.
      econstructor; autorewrite with upd; intros; eauto.
      apply Lt.le_lt_or_eq in H0; intuition subst.
      specialize (equal_after_holds0 a' ltac:(omega)).
      destruct matches in *|- ;
        autorewrite with upd;
        eauto.
      is_eq a a';
        autorewrite with upd;
        repeat simpl_match;
        eauto.
      unfold maybe_holds, curr_val_eq in *;
        simpl_match; subst.
      erewrite diskUpdF_eq by eauto; auto.

      is_eq a a';
        autorewrite with upd;
        repeat simpl_match;
        auto.

      destruct (d_0 a') eqn:?, (d_1 a') eqn:?; simpl in *;
        autorewrite with upd;
        unfold disk_get in *;
        try solve [ exfalso; eauto using same_size_disks_not_different ].
      erewrite diskUpdF_eq; eauto.
      simpl_match; auto.
    Qed.

    Hint Resolve equal_after_upd.

    Lemma crashesTo_one'_curr_val : forall d0__i d1__i d a v,
        crashesTo_one_of' d0__i d1__i d ->
        d a |= curr_val_eq v ->
        forall bs0 bs1, d0__i a = Some bs0 ->
                   d1__i a = Some bs1 ->
                   In v (durable_vals bs0) \/
                   In v (durable_vals bs1).
    Proof.
      intros.
      apply crashesTo_one'_pointwise with (a:=a) in H.
      repeat simpl_match.
      unfold curr_val_eq in *.
      destruct matches in *; simpl in *; try contradiction.
      intuition (subst; eauto).
    Qed.

    Lemma crashesTo_one_of'_upd:
      forall (a : nat) (d0__i d1__i : histdisk) (d_0 : diskOf blockhist) (d_1 : histdisk),
        crashesTo_one_of' d0__i d1__i d_0 ->
        crashesTo_one_of' d0__i d1__i d_1 ->
        forall v : block,
          d_0 a |= curr_val_eq v ->
          crashesTo_one_of' d0__i d1__i (diskUpdF d_1 a (buffer v)).
    Proof.
      intros.
      destruct H, H0.
      econstructor;
        autorewrite with upd; try congruence.
      intros.
      repeat match goal with
             | [ H: forall (_:addr), _ |- _ ] =>
               specialize (H a0)
             end.
      destruct matches in *|-; autorewrite with upd; eauto.
      is_eq a a0; autorewrite with upd in *.
      - unfold maybe_holds, curr_val_eq in *; repeat simpl_match; subst.
        erewrite diskUpdF_eq by eauto.
        autorewrite with block in *.
        safe_intuition eauto.
        split; eauto.
        eauto using contains_Add.
      - simpl_match.
        intuition eauto.
      - is_eq a a0; autorewrite with upd;
          repeat simpl_match;
          auto.
    Qed.

    Hint Resolve crashesTo_one_of'_upd.

    Definition state_hist (bs:blockstate) : blockhist :=
      {| current_val := curr_val bs;
         durable_vals := Add (curr_val bs)
                           (Singleton (durable_val bs));
         durable_includes_current := ltac:(auto); |}.

    Definition covering (d:disk) : histdisk :=
      mapDisk state_hist d.

    Lemma collapsesTo_state_hist : forall b,
        collapsesTo (state_hist b) b.
    Proof.
      unfold state_hist; destruct b; simpl; intros.
      econstructor; simpl; eauto.
    Qed.

    Lemma covered_covering : forall d,
        covered (covering d) d.
    Proof.
      intros.
      eapply pointwise_rel_indomain; intros; auto.
      simpl in *; repeat simpl_match.
      inversion H0; subst.
      eauto using collapsesTo_state_hist.
    Qed.

    Theorem crashesTo_covering_flushed : forall d,
        disk_flushed d ->
        crashesTo (covering d) d.
    Proof.
      intros.
      econstructor; intros; simpl; eauto.
      apply pointwise_prop_holds with (a:=a) in H.
      destruct matches.
      unfold block_flushed in *.
      destruct b; simpl in *; subst.
      econstructor; eauto.
      unfold state_hist; autorewrite with block; simpl.
      eauto.
    Qed.

    Hint Resolve crashesTo_covering_flushed.

    Lemma covering_flushed_flushed : forall d,
        disk_flushed d ->
        histdisk_flushed (covering d).
    Proof.
      destruct 1; intros.
      econstructor; intros.
      specialize (pointwise_prop_holds a).
      simpl.
      destruct matches.
      unfold block_flushed, hist_flushed, state_hist in *.
      destruct b; simpl in *; subst;
        autorewrite with block;
        simpl.
      eapply Ensemble_ext.
      split; intuition eauto.
      eapply Add_inv in H; intuition.
    Qed.

    Hint Resolve covering_flushed_flushed.

    Lemma crashesTo_one_of'_covering : forall d0__i d1__i d d',
        crashesTo d d' ->
        crashesTo_one_of' d0__i d1__i d ->
        crashesTo_one_of' d0__i d1__i (covering d').
    Proof.
      intros.
      destruct H, H0.
      econstructor; simpl; try congruence; intros.
      repeat match goal with
             | [ H: forall (_:addr), _ |- _ ] =>
               specialize (H a)
             end.
      destruct matches in *; try contradiction.
      inversion pointwise_rel_holds; subst; clear pointwise_rel_holds.
      unfold state_hist.
      autorewrite with block; simpl.
      rewrite Add_element by eauto.
      rewrite contains_Singleton.
      simpl.
      safe_intuition.
      apply H1 in H.
      eauto.
    Qed.

    Theorem crashesTo_one_of'_flush : forall d d0__i d1__i d',
        crashesTo d d' ->
        crashesTo_one_of' d0__i d1__i d ->
        exists d'',
          crashesTo d'' d' /\
          crashesTo_one_of' d0__i d1__i d'' /\
          histdisk_flushed d''.
    Proof.
      intros.
      exists (covering d');
        intuition eauto using crashesTo_one_of'_covering.
    Qed.

    Theorem fixup_ok : forall a,
        prog_spec
          (fun '(d0__i, d1__i) state =>
             {|
               pre :=
                 exists d_0 d_1,
                 a < size d_0 /\
                 TD.disk0 state |= covered d_0 /\
                 TD.disk1 state |= covered d_1 /\
                 equal_after (S a) d_0 d_1 /\
                 crashesTo_one_of' d0__i d1__i d_0 /\
                 crashesTo_one_of' d0__i d1__i d_1;
               post :=
                 fun r state' =>
                   match r with
                   | Continue =>
                     exists d_0' d_1',
                     TD.disk0 state' |= covered d_0' /\
                     TD.disk1 state' |= covered d_1' /\
                     equal_after a d_0' d_1' /\
                     crashesTo_one_of' d0__i d1__i d_0' /\
                     crashesTo_one_of' d0__i d1__i d_1'
                   | DiskFailed d0 =>
                     exists d_1',
                     TD.disk0 state' |= covered d_1' /\
                     TD.disk1 state' |= covered d_1' /\
                     crashesTo_one_of' d0__i d1__i d_1'
                   | DiskFailed d1 =>
                     exists d_0',
                     TD.disk0 state' |= covered d_0' /\
                     TD.disk1 state' |= covered d_0' /\
                     crashesTo_one_of' d0__i d1__i d_0'
                   end;
               recover :=
                 fun (_:unit) state' =>
                   (* either disk could change due to failures *)
                   exists d_0' d_1',
                     TD.disk0 state' |= crashesTo d_0' /\
                     TD.disk1 state' |= crashesTo d_1' /\
                     crashesTo_one_of' d0__i d1__i d_0' /\
                     crashesTo_one_of' d0__i d1__i d_1';
             |})
          (fixup a)
          (irec td)
          (refinement td).
    Proof.
      unfold fixup.
      step.
      descend; intuition eauto.

      destruct r; try step.
      descend; intuition eauto.

      destruct r; try step.
      descend; intuition eauto.

      is_eq v v0; try step.
      intuition.
      descend; intuition eauto.
      descend; intuition eauto.

      descend; intuition eauto.
      step.
      destruct matches; simplify.
      intuition.
      descend; intuition eauto.
      descend; intuition eauto.

      intuition.
      descend; intuition eauto.
      descend; intuition eauto.
      descend; intuition eauto.
      descend; intuition eauto.

      intuition.
      descend; intuition eauto.
      descend; intuition eauto.
      descend; intuition eauto.

      intuition.
      descend; intuition eauto.
      descend; intuition eauto.
      descend; intuition eauto.
    Qed.

    Hint Resolve fixup_ok.

    Lemma lt_S_trans : forall a b,
        S a < b ->
        a < b.
    Proof.
      intros.
      omega.
    Qed.

    Hint Resolve lt_S_trans.

    Theorem recover_at_ok : forall a,
        prog_spec
          (fun '(d0__i, d1__i) state =>
             {|
               pre :=
                 exists d_0 d_1,
                 a < size d_0 /\
                 TD.disk0 state |= covered d_0 /\
                 TD.disk1 state |= covered d_1 /\
                 equal_after a d_0 d_1 /\
                 crashesTo_one_of' d0__i d1__i d_0 /\
                 crashesTo_one_of' d0__i d1__i d_1;
               post :=
                 fun r state' =>
                   match r with
                   | Continue =>
                     exists d_0' d_1',
                     TD.disk0 state' |= covered d_0' /\
                     TD.disk1 state' |= covered d_1' /\
                     equal_after 0 d_0' d_1' /\
                     crashesTo_one_of' d0__i d1__i d_0' /\
                     crashesTo_one_of' d0__i d1__i d_1'
                   | DiskFailed d0 =>
                     exists d_1',
                     TD.disk0 state' |= covered d_1' /\
                     TD.disk1 state' |= covered d_1' /\
                     crashesTo_one_of' d0__i d1__i d_1'
                   | DiskFailed d1 =>
                     exists d_0',
                     TD.disk0 state' |= covered d_0' /\
                     TD.disk1 state' |= covered d_0' /\
                     crashesTo_one_of' d0__i d1__i d_0'
                   end;
               recover :=
                 fun (_:unit) state' =>
                   (* either disk could change due to failures *)
                   exists d_0' d_1',
                     TD.disk0 state' |= crashesTo d_0' /\
                     TD.disk1 state' |= crashesTo d_1' /\
                     crashesTo_one_of' d0__i d1__i d_0' /\
                     crashesTo_one_of' d0__i d1__i d_1';
             |})
          (recover_at a)
          (irec td)
          (refinement td).
    Proof.
      induction a; simpl.
      - step.
        descend; (intuition eauto); simplify; finish.
      - step.
        descend; (intuition eauto); simplify; finish.

        destruct r; step.
        descend; (intuition eauto); simplify; finish.
        exists d_0', d_1'; intuition eauto.
        assert (size d_0' = size d_0) as Hsize.
        repeat match goal with
               | [ H: crashesTo_one_of' _ _ _ |- _ ] =>
                 destruct H
               end; congruence.
        rewrite Hsize; eauto.
        destruct i; simplify; finish.
    Qed.

    (* crashesTo_one_of d_0 d_1 d says [forall a, d_0(a) ~> d(a) \/ d_1(a) ~> d(a)]
    where [h ~> h'] is made-up notation for h crashing to the current value in
    h' (with h also having durable values from the union of d_0(a) and d_1(a)).

     This isn't a pointwise_rel, unfortunately, since it covers three disks. *)
    Record crashesTo_one_of (d_0 d_1 d:histdisk) : Prop :=
      { crashesTo_one_size0 : size d_0 = size d;
        crashesTo_one_size1 : size d_1 = size d;
        crashesTo_one_pointwise : forall a,
            match d_0 a, d_1 a, d a with
            | Some h0, Some h1, Some h => In (curr_val h) (durable_vals h0) \/
                                          In (curr_val h) (durable_vals h1)
            | None, None, None => True
            | _, _, _ => False
            end;
      }.

    Definition Recover_spec :=
      (fun '(d_0, d_1) state =>
         {|
           pre :=
             TD.disk0 state |= crashesTo d_0 /\
             TD.disk1 state |= crashesTo d_1 /\
             (* we put this later to help sequential eauto calls from
             instantiating d_1 to d_0 *)
             size d_0 = size d_1;
           post :=
             fun (_:unit) state' =>
               exists d,
                 TD.disk0 state' |= crashesTo d /\
                 TD.disk1 state' |= crashesTo d /\
                 crashesTo_one_of d_0 d_1 d /\
                 histdisk_flushed d;
           recover :=
             fun (_:unit) state' =>
               (* either disk could change due to failures *)
               exists d_0' d_1',
                 TD.disk0 state' |= crashesTo d_0' /\
                 TD.disk1 state' |= crashesTo d_1' /\
                 crashesTo_one_of d_0 d_1 d_0' /\
                 crashesTo_one_of d_0 d_1 d_1' /\
                 histdisk_flushed d_0' /\
                 histdisk_flushed d_1';
         |}).

    Theorem Recover_rok :
      prog_spec
        Recover_spec
        (Recover)
        (irec td)
        (refinement td).
    Proof.
    Admitted.

    Lemma histblock_trans : forall h h',
        In (curr_val h') (durable_vals h) ->
        hist_flushed h' ->
        forall h'', In (curr_val h'') (durable_vals h') ->
               In (curr_val h'') (durable_vals h).
    Proof.
      unfold hist_flushed; intros.
      rewrite H0 in *.
      apply Singleton_inv in H1.
      congruence.
    Qed.

    Hint Resolve histblock_trans.

    Lemma crashesTo_one_of_trans:
      forall d_0 d_1 d_0' d_1' : histdisk,
        crashesTo_one_of d_0 d_1 d_0' ->
        crashesTo_one_of d_0 d_1 d_1' ->
        histdisk_flushed d_0' ->
        histdisk_flushed d_1' ->
        forall d' : histdisk,
          crashesTo_one_of d_0' d_1' d' ->
          crashesTo_one_of d_0 d_1 d'.
    Proof.
      intros.
      repeat match goal with
             | [ H: histdisk_flushed _ |- _ ] => destruct H
             | [ H: crashesTo_one_of _ _ _ |- _ ] => destruct H
             end.
      econstructor; intros; try congruence.
      repeat match goal with
             | [ H: forall (_:addr), _ |- _ ] =>
               specialize (H a)
             end.
      destruct matches in *; try contradiction; intuition eauto.
    Qed.

    Hint Resolve crashesTo_one_of_trans.

    Theorem Recover_ok :
      prog_loopspec
        Recover_spec
        (Recover)
        (irec td)
        (refinement td).
    Proof.
      eapply idempotent_loopspec; simpl.
      - eapply Recover_rok.
      - unfold idempotent; intuition; simplify.
        descend; intuition eauto.
        repeat match goal with
               | [ H: crashesTo_one_of _ _ _ |- _ ] =>
                 destruct H
               end; congruence.
        repeat deex.
        descend; intuition eauto.
    Qed.

End AsyncReplicatedDisk.
