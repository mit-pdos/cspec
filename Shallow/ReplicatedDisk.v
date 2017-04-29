Require Import FunctionalExtensionality.

Require Import Disk.
Require Import Automation.

Require Import Shallow.ProgLang.Prog.
Require Import Shallow.ProgLang.Hoare.
Require Import Shallow.TwoDiskProg.
Require Import Shallow.SeqDiskProg.

Require Import Interpret.

Module RD.

  Definition Read (a:addr) : TD.prog block :=
    mv0 <- Prim (TD.Read d0 a);
      match mv0 with
      | Working v => Ret v
      | Failed => mv2 <- Prim (TD.Read d1 a);
                   match mv2 with
                   | Working v => Ret v
                   | Failed => Ret block0
                   end
      end.

  Definition Write (a:addr) (b:block) : TD.prog unit :=
    _ <- Prim (TD.Write d0 a b);
      _ <- Prim (TD.Write d1 a b);
      Ret tt.

  Definition op_impl T (op:D.Op T) : TD.prog T :=
    match op with
    | D.Read a => Read a
    | D.Write a b => Write a b
    end.

  Definition interpret := Interpret.interpret op_impl.

  Definition abstraction (state:TD.State) : D.State.
  Proof.
    destruct state.
    destruct disk0.
    exact (D.Disk d).
    destruct disk1.
    exact (D.Disk d).
    exfalso.
    abstract (deex; intuition; congruence).
  Defined.

  Definition invariant (state:TD.State) :=
    match state with
    | TD.Disks (Some d_0) (Some d_1) _ =>
      d_0 = d_1
    | _ => True
    end.

  Lemma invariant_stable_bg_step : forall state state',
      invariant state ->
      TD.bg_step state state' ->
      invariant state'.
  Proof.
    inversion 2; intros; subst;
      simpl; eauto.
  Qed.

  Hint Resolve invariant_stable_bg_step.

  Lemma abstraction_preserved_bg_step : forall state state',
      invariant state ->
      TD.bg_step state state' ->
      abstraction state' = abstraction state.
  Proof.
    inversion 2; subst; simpl in *; subst; eauto.
  Qed.

  Lemma abstraction_d0_eq : forall state d a v,
      TD.disk0 state = Some d ->
      d a = v ->
      D.sdisk (abstraction state) a = v.
  Proof.
    intros; subst.
    unfold abstraction.
    destruct matches; simpl in *; try congruence.
  Qed.

  Definition first_disk_failed state :=
    TD.disk0 state = None.

  Lemma abstraction_d1_eq : forall state d a v,
      first_disk_failed state ->
      TD.disk1 state = Some d ->
      d a = v ->
      D.sdisk (abstraction state) a = v.
  Proof.
    unfold first_disk_failed; intros; subst.
    unfold abstraction.
    destruct matches; simpl in *; try congruence.
  Qed.

  Hint Resolve abstraction_preserved_bg_step.

  Theorem TDRead0_ok : forall a,
      prog_spec
        (fun (_:unit) (state:TD.State) =>
           {|
             pre := invariant state;
             post :=
               fun r state' =>
                 abstraction state' = abstraction state /\
                 invariant state' /\
                 match r with
                 | Working v => forall v0, D.sdisk (abstraction state) a = Some v0 ->
                                     v = v0
                 | Failed => first_disk_failed state'
                 end;
             crash := fun state' => abstraction state' = abstraction state;
           |})
        (Prim (TD.Read d0 a))
        TD.step.
  Proof.
    intros.
    unfold prog_spec; simpl; intros.
    inv_exec; eauto.
    TD.inv_step; cbn [TD.get_disk] in *.
    intuition eauto.

    destruct matches in *|-; intros; eauto.
    eapply abstraction_d0_eq in Heqo; eauto.
    erewrite abstraction_preserved_bg_step in * by eauto.
    congruence.

    repeat deex; intros; eauto.
    eapply abstraction_d0_eq in Heqo; eauto.
    erewrite abstraction_preserved_bg_step in * by eauto.
    congruence.

    TD.inv_step.
    intuition eauto.
  Qed.

  Lemma bg_step_after_fail : forall state state',
      first_disk_failed state ->
      TD.bg_step state state' ->
      state' = state.
  Proof.
    unfold first_disk_failed.
    inversion 2; subst; simpl in *;
      congruence.
  Qed.

  Lemma first_disk_failed_other_not_none : forall state,
      first_disk_failed state ->
      ~TD.disk1 state = None.
  Proof.
    unfold first_disk_failed; destruct state; simpl; intros.
    deex; intuition congruence.
  Qed.

  Theorem TDRead1_ok : forall a,
      prog_spec
        (fun (_:unit) (state:TD.State) =>
           {|
             pre := invariant state /\
                    first_disk_failed state;
             post :=
               fun r state' =>
                 abstraction state' = abstraction state /\
                 invariant state' /\
                 match r with
                 | Working v => forall v0, D.sdisk (abstraction state) a = Some v0 ->
                                     v = v0
                 | Failed => False
                 end;
             crash := fun state' => abstraction state' = abstraction state;
           |})
        (Prim (TD.Read d1 a))
        TD.step.
  Proof.
    unfold prog_spec; cbn [pre post crash]; intuition.
    inv_exec; eauto.
    TD.inv_step; cbn [TD.get_disk] in *.
    intuition eauto.
    eapply bg_step_after_fail in H; eauto; subst.

    destruct matches in *|-; intros; eauto.
    eapply abstraction_d1_eq in Heqo; eauto.
    congruence.

    repeat deex; intros; eauto.
    eapply abstraction_d1_eq in Heqo; eauto.
    congruence.

    eapply first_disk_failed_other_not_none; eauto.

    TD.inv_step.
    intuition eauto.
  Qed.

  Hint Resolve tt.

  Hint Constructors D.step.

  Lemma abstraction_set_d0 : forall state d a b,
      TD.get_disk d0 state = Some d ->
      abstraction (TD.set_disk d0 state (upd d a b)) =
      D.Disk (upd (D.sdisk (abstraction state)) a b).
  Proof.
    intros.
    destruct state; simpl in *.
    destruct disk0; simpl; congruence.
  Qed.

  Definition invariant_except (state:TD.State) a b :=
    match state with
    | TD.Disks (Some d_0) (Some d_1) _ =>
      (exists b0, d_1 a = Some b0) /\
      d_0 = upd d_1 a b
    | TD.Disks (Some d_0) None _ =>
      d_0 a = Some b
    | TD.Disks None (Some _) _ => False
    | _ => True
    end.

  Lemma invariant_except_upd_d0 : forall state d a b0 b,
      invariant state ->
      TD.disk0 state = Some d ->
      d a = Some b0 ->
      invariant_except (TD.set_disk d0 state (upd d a b)) a b.
  Proof.
    unfold invariant, invariant_except; intros.
    destruct matches in *|- ;
      simpl in *;
      intuition;
      try congruence.
    match goal with
    | [ H: Some _ = Some _ |- _ ] =>
      inversion H; subst; clear H
    end; eauto.
    autorewrite with upd; auto.
  Qed.

  Hint Resolve invariant_except_upd_d0.

  Lemma abstraction_is_some_disk : forall state,
      {exists d, TD.get_disk d0 state = Some d /\
            abstraction state = D.Disk d} +
      {exists d, TD.get_disk d1 state = Some d /\
            abstraction state = D.Disk d /\
            TD.get_disk d0 state = None}.
  Proof.
    intros.
    destruct state; simpl.
    destruct matches;
      eauto.
    exfalso; repeat deex; intuition congruence.
  Qed.

  Ltac case_abstraction :=
    match goal with
    | [ H: context[D.sdisk (abstraction ?state)] |- _ ] =>
      destruct (abstraction_is_some_disk state);
      repeat deex;
      match goal with
      | [ H: abstraction _ = _ |- _ ] =>
        rewrite H in *; cbn [D.sdisk] in *
      end
    end.

  Lemma invariant_stability : forall state state',
      invariant state ->
      TD.bg_step state state' ->
      abstraction state = abstraction state' /\
      invariant state'.
  Proof.
    intros.
    intuition eauto.
    symmetry; auto.
  Qed.

  Ltac inv_stable :=
    match goal with
    | [ H: invariant ?state,
           H': TD.bg_step ?state ?state' |- _ ] =>
      pose proof (invariant_stability H H');
      clear H H';
      safe_intuition;
      replace (abstraction state) in *
    end.

  Theorem TDWrite0_inbounds_ok : forall a b,
      prog_spec
        (fun b0 (state:TD.State) =>
           {|
             pre := invariant state /\
                    D.sdisk (abstraction state) a = Some b0;
             post :=
               fun r state' =>
                 (abstraction state' = D.Disk (upd (D.sdisk (abstraction state)) a b) /\
                  invariant_except state' a b) \/
                 (abstraction state' = abstraction state /\
                  first_disk_failed state');
             crash :=
               fun state' =>
                 (abstraction state' = abstraction state /\
                  invariant state') \/
                 (abstraction state' = D.Disk (upd (D.sdisk (abstraction state)) a b) /\
                  (* this should be a recoverable property *)
                  invariant_except state' a b)
           |})
        (Prim (TD.Write d0 a b))
        TD.step.
  Proof.
    unfold prog_spec; cbn [pre post crash]; intuition.
    inv_exec; eauto.
    - TD.inv_step.
      subst_var.
      inv_stable.
      case_abstraction;
        repeat simpl_match;
        eauto.
      rewrite abstraction_set_d0 by auto.
      replace (abstraction x); cbn [D.sdisk]; eauto.
    - TD.inv_step; subst_var.
      inv_stable.
      case_abstraction;
        repeat simpl_match;
        eauto.
      rewrite abstraction_set_d0 by auto.
      replace (abstraction x); cbn [D.sdisk]; eauto.
  Qed.

  Lemma invariant_both_disks : forall state d_0 d_1,
      invariant state ->
      TD.get_disk d0 state = Some d_0 ->
      TD.get_disk d1 state = Some d_1 ->
      d_0 = d_1.
  Proof.
    unfold invariant; intros; destruct matches in *;
      simpl in *;
      congruence.
  Qed.

  Theorem TDWrite_oob_ok : forall i a b,
      prog_spec
        (fun (_:unit) (state:TD.State) =>
           {|
             pre := invariant state /\
                    D.sdisk (abstraction state) a = None;
             post :=
               fun r state' =>
                 abstraction state' = abstraction state /\
                 invariant state';
             crash :=
               fun state' =>
                 abstraction state' = abstraction state /\
                 invariant state'
           |})
        (Prim (TD.Write i a b))
        TD.step.
  Proof.
    unfold prog_spec; cbn [pre post crash]; intuition.
    inv_exec; eauto.
    - TD.inv_step.
      subst_var.
      inv_stable.
      destruct i; case_abstraction;
        repeat simpl_match;
        eauto.
      destruct (TD.get_disk d1 x) eqn:?; eauto.
      pose proof (invariant_both_disks _ H0 ltac:(eauto) ltac:(eauto));
        subst.
      simpl_match; eauto.
    - TD.inv_step.
      subst_var.
      inv_stable.
      destruct i; case_abstraction;
        repeat simpl_match;
        eauto.
      destruct (TD.get_disk d1 x) eqn:?; eauto.
      pose proof (invariant_both_disks _ H0 ltac:(eauto) ltac:(eauto));
        subst.
      simpl_match; eauto.
  Qed.

  Theorem invariant_except_step : forall state a b state',
      invariant_except state a b ->
      TD.bg_step state state' ->
      (invariant_except state' a b \/
       invariant state').
  Proof.
    inversion 2; subst; simpl in *; eauto.
  Qed.

  Hint Resolve invariant_except_step.

  Lemma invariant_except_to_invariant : forall state d a b,
      invariant_except state a b ->
      TD.get_disk d1 state = Some d ->
      invariant (TD.set_disk d1 state (upd d a b)).
  Proof.
    unfold invariant_except; intros.
    destruct state; simpl in *; subst; auto.
    destruct matches; safe_intuition; eauto.
  Qed.

  Hint Resolve invariant_except_to_invariant.

  Ltac cleanup :=
    repeat match goal with
           | _ => progress safe_intuition
           | _ => simpl_match
           | _ => deex
           | _ => progress subst
           | _ => progress simpl in *
           | _ => contradiction
           | [ H: None = Some _ \/ None = Some _ |- _ ] =>
             exfalso; destruct H; congruence
           | [ H: Some _ = Some _ |- _ ] =>
             inversion H; subst; clear H
           | _ => progress eauto
           | _ => congruence
           end.

  Lemma invariant_except_after_step : forall state state' a b,
      invariant_except state a b ->
      TD.bg_step state state' ->
      (* d0 survived *)
      (exists d, TD.get_disk d0 state' = Some d /\
            abstraction state' = D.Disk d /\
            d a = Some b /\
            invariant_except state' a b) \/
      (* only d1 survived *)
      (exists b0 d, TD.get_disk d1 state' = Some d /\
               abstraction state' = D.Disk d /\
               d a = Some b0 /\
               TD.get_disk d0 state' = None).
  Proof.
    inversion 2; cleanup; eauto 10 using upd_eq.
    unfold invariant_except in H; destruct matches in *;
      cleanup;
      eauto 10 using upd_eq.
  Qed.

  Lemma invariant_except_set_d1 : forall state d' a b,
      invariant_except state a b ->
      abstraction (TD.set_disk d1 state d') = abstraction state.
  Proof.
    intros.
    unfold invariant_except, abstraction in *;
      destruct matches in *;
      simpl in *;
      try match goal with
          | [ H: TD.Disks _ _ _ = TD.Disks _ _ _ |- _ ] =>
            inversion H; subst; clear H
          end;
      cleanup.
  Qed.

  Lemma invariant_except_known_d0 : forall state d a b,
      TD.get_disk d0 state = Some d ->
      invariant_except state a b ->
      (TD.get_disk d1 state = None \/
       exists b0 d', TD.get_disk d1 state = Some d' /\
             d' a = Some b0 /\
             d = upd d' a b).
  Proof.
    unfold invariant_except; intros.
    destruct matches in *; cleanup.
    eauto 10.
  Qed.

  Lemma bg_step_invert : forall state d_0 d_1 pf,
      TD.bg_step state (TD.Disks (Some d_0) (Some d_1) pf) ->
      state = TD.Disks (Some d_0) (Some d_1) pf.
  Proof.
    intros.
    inversion H; subst; eauto.
  Qed.

  Lemma invariant_except_no_d1 : forall state a b,
      invariant_except state a b ->
      TD.disk1 state = None ->
      invariant state.
  Proof.
    unfold invariant_except; intros;
      destruct matches in *;
      cleanup.
  Qed.

  Hint Resolve invariant_except_no_d1.

  Theorem TDWrite1_inbounds_d0_ok : forall a b,
      prog_spec
        (fun (_:unit) (state:TD.State) =>
           {|
             pre := invariant_except state a b;
             post :=
               fun r state' =>
                 abstraction state' = abstraction state /\
                 invariant state';
             crash :=
               fun state' =>
                 (abstraction state' = abstraction state /\
                  invariant_except state' a b) \/
                 (abstraction state' = abstraction state /\
                  invariant state')
                 (* missing crash case: we might actually lose the first disk
                 and thus undo the pending write, but this isn't a possible
                 crash state; the fix is either to allow a bg_step right after
                 crash, to add a new crash state after a disk possibly fails but
                 before the write runs *)
                 (* (exists d, TD.disk1 state = Some d /\
                       abstraction state' = D.Disk d) *);
           |})
        (Prim (TD.Write d1 a b))
        TD.step.
  Proof.
    unfold prog_spec; cbn [pre post crash]; intuition.
    inv_exec; eauto.
    - TD.inv_step.
      subst_var.
      destruct (invariant_except_after_step _ _ H H0);
        repeat deex.
      destruct (invariant_except_known_d0 _ _ _ H1 H4);
        cleanup.
      inversion H0; cleanup; intuition eauto.

      destruct matches; simpl in *; destruct matches in *;
        cleanup;
        intuition eauto.
      eapply bg_step_invert in H0; subst; simpl; eauto.

      destruct matches; simpl in *; destruct matches in *;
        cleanup;
        intuition eauto.
      destruct disk0, disk1; cleanup.
      inversion H0; subst; cleanup.
    - right.
      TD.inv_step.
      subst_var.
      destruct (invariant_except_after_step _ _ H H0);
        repeat deex.
      destruct (invariant_except_known_d0 _ _ _ H1 H4);
        cleanup.
      inversion H0; cleanup; intuition eauto.

      destruct matches; simpl in *; destruct matches in *;
        cleanup;
        intuition eauto.
      eapply bg_step_invert in H0; subst; simpl; eauto.

      destruct matches; simpl in *; destruct matches in *;
        cleanup;
        intuition eauto.
      destruct disk0, disk1; cleanup.
      inversion H0; subst; cleanup.
  Qed.

  Theorem TDWrite1_inbounds_no_d0_ok : forall a b,
      prog_spec
        (fun b0 (state:TD.State) =>
           {|
             pre := invariant state /\
                    first_disk_failed state /\
                    D.sdisk (abstraction state) a = Some b0;
             post :=
               fun r state' =>
                 abstraction state' = D.Disk (upd (D.sdisk (abstraction state)) a b) /\
                 invariant state';
             crash :=
               fun state' =>
                 (abstraction state' = abstraction state /\
                  invariant state') \/
                 (abstraction state' = D.Disk (upd (D.sdisk (abstraction state)) a b) /\
                 invariant state');
           |})
        (Prim (TD.Write d1 a b))
        TD.step.
  Proof.
    unfold prog_spec; cbn [pre post crash]; intuition.
    inv_exec; eauto.
    - TD.inv_step.
      subst_var.
      eapply bg_step_after_fail in H1; eauto; subst.
      case_abstraction;
        unfold first_disk_failed in *;
        cleanup.
      destruct matches in *;
        cleanup;
        destruct matches in *.
    - TD.inv_step.
      subst_var.
      eapply bg_step_after_fail in H1; eauto; subst.
      case_abstraction;
        unfold first_disk_failed in *;
        cleanup.
      destruct matches in *;
        cleanup;
        destruct matches in *.
  Qed.

  Lemma step_write_inbounds : forall state a b0 b,
      D.sdisk state a = Some b0 ->
      D.step (D.Write a b) state tt
             (D.Disk (upd (D.sdisk state) a b)).
  Proof.
    intros.
    pose proof (D.step_write a b state); simpl in *.
    simpl_match.
    auto.
  Qed.

  Hint Resolve step_write_inbounds.

  Lemma invariant_first_disk_failed : forall state,
      first_disk_failed state ->
      invariant state.
  Proof.
    unfold first_disk_failed, invariant;
      intros;
      destruct matches in *;
      cleanup.
  Qed.

  Hint Resolve invariant_first_disk_failed.

  Lemma step_write_oob : forall state a b,
      D.sdisk state a = None ->
      D.step (D.Write a b) state tt state.
  Proof.
    intros.
    pose proof (D.step_write a b state); simpl in *.
    simpl_match.
    destruct state; eauto.
  Qed.

  Hint Resolve step_write_oob.

  Theorem RD_ok : interpretation
                    op_impl
                    TD.step D.step
                    invariant
                    abstraction.
  Proof.
    eapply interpret_exec; intros; eauto.
    - destruct op; simpl in *; unfold Read, Write in *.
      + inv_exec.
        eapply TDRead0_ok in H6; cbn [pre post crash] in *;
          safe_intuition; eauto.
        destruct v0; safe_intuition;
          try inv_ret.
        repeat match goal with
               | [ H: _ = _ |- _ ] =>
                 rewrite H in *
               end.
        intuition eauto.

        inv_exec.
        eapply TDRead1_ok in H9; cbn [pre post crash] in *;
          safe_intuition; eauto.
        destruct v0; safe_intuition;
          try inv_ret;
          try contradiction.
        repeat match goal with
               | [ H: _ = _ |- _ ] =>
                 rewrite H in *
               end.
        intuition eauto.
      + inv_exec.
        destruct (D.sdisk (abstraction state) a) eqn:?.
        eapply TDWrite0_inbounds_ok in H6; eauto;
          cbn [pre post crash] in *;
          cleanup.
        hyp_intuition.
        inv_exec.
        eapply TDWrite1_inbounds_d0_ok in H7; eauto;
          cbn [pre post crash] in *;
          cleanup.
        repeat match goal with
               | [ H: abstraction _ = _ |- _ ] =>
                 rewrite H
               end.
        intuition eauto.

        inv_exec.
        eapply TDWrite1_inbounds_no_d0_ok in H7; eauto;
          cbn [pre post crash] in *;
          cleanup;
          repeat match goal with
                 | [ H: abstraction _ = _ |- _ ] =>
                   rewrite H
                 end;
          intuition eauto.

        eapply TDWrite_oob_ok in H6; eauto;
          cbn [pre post crash] in *;
          cleanup.
        inv_exec.
        eapply TDWrite_oob_ok in H7; eauto;
          cbn [pre post crash] in *;
          cleanup;
          repeat match goal with
                 | [ H: abstraction _ = _ |- _ ] =>
                   rewrite H
                 end;
          intuition eauto.
    - (* also need a crash proof *)
  Abort.

End RD.
