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

  Definition abstraction (state:TD.State) : D.State :=
    match state with
    | TD.Disks (Some d) _ _ => D.Disk d
    | TD.Disks None (Some d) _ => D.Disk d
    | _ => D.Disk empty_disk (* impossible *)
    end.

  Definition invariant (state:TD.State) :=
    match state with
    | TD.Disks (Some d_0) (Some d_1) _ =>
      d_0 = d_1
    | _ => True
    end.

  Lemma abstraction_d0 : forall state d,
      TD.disk0 state = Some d ->
      abstraction state = D.Disk d.
  Proof.
    unfold abstraction; intros.
    destruct state; simpl in *; subst; auto.
  Qed.

  Lemma abstraction_d1 : forall state d,
      TD.disk0 state = None ->
      TD.disk1 state = Some d ->
      abstraction state = D.Disk d.
  Proof.
    unfold abstraction; intros.
    destruct state; simpl in *; subst; auto.
  Qed.

  Lemma invariant_disks : forall state d,
      TD.disk0 state = Some d ->
      TD.disk1 state = Some d ->
      invariant state.
  Proof.
    intros.
    destruct state; simpl in *; subst; auto.
  Qed.

  Lemma invariant_d0 : forall state,
      TD.disk1 state = None ->
      invariant state.
  Proof.
    destruct state; simpl; intros; subst; eauto.
    destruct disk0; auto.
  Qed.

  Lemma invariant_d1 : forall state,
      TD.disk0 state = None ->
      invariant state.
  Proof.
    destruct state; simpl; intros; subst; eauto.
  Qed.

  Lemma invariant_disks_fwd : forall d_0 d_1 pf,
      invariant (TD.Disks (Some d_0) (Some d_1) pf) ->
      d_0 = d_1.
  Proof.
    simpl; eauto.
  Qed.

  Lemma invariant_disks_fwd_eq : forall state d_0 d_1,
      invariant state ->
      TD.disk0 state = Some d_0 ->
      TD.disk1 state = Some d_1 ->
      d_0 = d_1.
  Proof.
    destruct state; simpl; intros; repeat simpl_match; eauto.
  Qed.

  Lemma abstraction_set_d0 : forall state d',
      abstraction (TD.set_disk d0 state d') = D.Disk d'.
  Proof.
    destruct state; simpl; eauto.
  Qed.

  Opaque invariant.
  Opaque abstraction.

  Ltac find_contradiction :=
    solve [ exfalso; eauto ].

  Ltac cleanup :=
    repeat match goal with
           | [ |- forall _, _ ] => intros
           | _ => progress subst
           | _ => progress simpl in *
           | _ => deex
           | _ => progress destruct_ands
           | [ |- invariant (TD.Disks None _ _) ] =>
             now apply invariant_d1
           | [ |- invariant (TD.Disks _ None _) ] =>
             now apply invariant_d0
           | [ H: invariant (TD.Disks (Some _) (Some _) _) |- _ ] =>
             apply invariant_disks_fwd in H
           | [ H: invariant ?state,
                  H0: TD.disk0 ?state = Some _,
                      H1: TD.disk1 ?state = Some _ |- _ ] =>
             pose proof (invariant_disks_fwd_eq _ H H0 H1);
             clear H0 H1;
             subst
           | [ H: Some _ = Some _ |- _ ] =>
             inversion H; subst; clear H
           | _ => simpl_match
           | _ => solve [ eauto ]
           | _ => find_contradiction
           | _ => congruence
           end.

  Lemma invariant_stable : forall state state',
      invariant state ->
      TD.bg_step state state' ->
      invariant state'.
  Proof.
    inversion 2; cleanup.
  Qed.

  Hint Resolve invariant_stable.

  Lemma abstraction_stable_invariant : forall state state',
      invariant state ->
      TD.bg_step state state' ->
      abstraction state' = abstraction state.
  Proof.
    inversion 2; cleanup.
  Qed.

  Ltac abstraction_fwd :=
    match goal with
    | [ H: invariant ?state,
           H': TD.bg_step ?state ?state' |- _ ] =>
      rewrite <- (abstraction_stable_invariant H H') in *
    end.

  Lemma d0_failed_fwd : forall state state',
      TD.disk0 state = None ->
      TD.bg_step state state' ->
      state' = state.
  Proof.
    inversion 2; cleanup.
  Qed.

  Lemma d0_d1_failed : forall state,
      TD.disk0 state = None ->
      TD.disk1 state = None ->
      False.
  Proof.
    destruct state; cleanup.
    intuition congruence.
  Qed.

  Hint Resolve d0_d1_failed.

  Ltac inv_fwd :=
    match goal with
    | [ H: TD.disk0 ?state = None,
           H': TD.bg_step ?state ?state' |- _ ] =>
      eapply d0_failed_fwd in H'; eauto; subst
    | [ H: invariant ?state,
           H': TD.bg_step ?state ?state' |- _ ] =>
      pose proof (invariant_stable H H')
    end.

  Ltac abstraction_simpl :=
    try (progress erewrite ?abstraction_d0,
         ?abstraction_d1 in * by (simpl; eauto);
         cbn [ D.sdisk ] in * ).

  Ltac start_spec :=
    unfold prog_spec; cbn [pre post crash] in *; intros;
    match goal with
    | [ H: exec _ (Prim _) _ _ |- _ ] =>
      eapply (inversion_prim_exec H); intros
    | _ => inv_exec
    end; try solve [ intuition eauto ].

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
                 | Working v => forall v0, diskMem (D.sdisk (abstraction state)) a = Some v0 ->
                                     v = v0
                 | Failed => TD.disk0 state' = None
                 end;
             crash := fun state' =>
                        abstraction state' = abstraction state /\
                        invariant state';
           |})
        (Prim (TD.Read d0 a))
        TD.step.
  Proof.
    start_spec.
    TD.inv_step; cbn [TD.get_disk] in *.
    destruct matches in *|-; cleanup;
      try abstraction_fwd;
      try inv_fwd;
      abstraction_simpl;
      try intuition (eauto; congruence).
  Qed.

  Theorem TDRead1_ok : forall a,
      prog_spec
        (fun (_:unit) (state:TD.State) =>
           {|
             pre := invariant state /\
                    TD.disk0 state = None;
             post :=
               fun r state' =>
                 abstraction state' = abstraction state /\
                 invariant state' /\
                 match r with
                 | Working v => forall v0, diskMem (D.sdisk (abstraction state)) a = Some v0 ->
                                     v = v0
                 | Failed => False
                 end;
             crash := fun state' =>
                        abstraction state' = abstraction state /\
                        invariant state';
           |})
        (Prim (TD.Read d1 a))
        TD.step.
  Proof.
    start_spec.
    TD.inv_step; cbn [TD.get_disk] in *.
    destruct matches in *|-; cleanup;
      try abstraction_fwd;
      try inv_fwd;
      abstraction_simpl;
      try intuition (eauto; congruence).
  Qed.

  Ltac rew_abstraction :=
    repeat match goal with
           | [ H: abstraction _ = _ |- _ ] =>
             rewrite H in *
           end.

  Theorem Read_ok : forall a,
      prog_spec
        (fun (_:unit) (state:TD.State) =>
           {|
             pre := invariant state;
             post :=
               fun r state' =>
                 (forall v, diskMem (D.sdisk (abstraction state')) a = Some v ->
                       r = v) /\
                 abstraction state' = abstraction state /\
             invariant state';
             crash :=
               fun state' => abstraction state' = abstraction state /\
                      invariant state';
           |})
        (Read a)
        TD.step.
  Proof.
    start_spec.
    - eapply TDRead0_ok in H6; cbn [pre post crash] in *;
        cleanup.
      destruct v.
      inv_exec; cleanup; rew_abstraction; eauto.

      inv_exec; cleanup.
      eapply TDRead1_ok in H9; cbn [pre post crash] in *;
        cleanup.
      destruct v; cleanup.

      inv_exec; rew_abstraction; cleanup.

      eapply TDRead1_ok in H9; cbn [pre post crash] in *;
        cleanup.
      intuition eauto.
      congruence.
    - eapply TDRead0_ok in H6; cbn [pre post crash] in *;
        cleanup.
  Qed.

  Hint Resolve tt.

  Hint Constructors D.step.

  Definition d0_upd (state:TD.State) a b :=
    match state with
    | TD.Disks (Some d_0) (Some d_1) _ =>
      (exists b0, d_1 a = Some b0) /\
      d_0 = diskUpd d_1 a b
    | TD.Disks (Some d_0) None _ =>
      d_0 a = Some b
    | TD.Disks None (Some _) _ => False
    | _ => False
    end.

  Lemma d0_upd_set_d0 : forall state d a b b0,
      invariant state ->
      TD.disk0 state = Some d ->
      d a = Some b0 ->
      d0_upd (TD.set_disk d0 state (diskUpd d a b)) a b.
  Proof.
    intros.
    destruct state; cleanup.
    destruct disk1; cleanup.
    erewrite diskUpd_eq_some; eauto.
  Qed.

  Lemma d0_upd_to_invariant : forall state d a b,
      d0_upd state a b ->
      TD.get_disk d1 state = Some d ->
      invariant (TD.set_disk d1 state (diskUpd d a b)).
  Proof.
    destruct state; cleanup.
    destruct disk0; cleanup.
  Qed.

  Lemma abstraction_set_d1_with_d0 : forall state d d',
      TD.disk0 state = Some d ->
      abstraction (TD.set_disk d1 state d') = abstraction state.
  Proof.
    destruct state; cleanup.
  Qed.

  Lemma abstraction_set_d1 : forall state d',
      TD.disk0 state = None ->
      abstraction (TD.set_disk d1 state d') = D.Disk d'.
  Proof.
    destruct state; cleanup.
  Qed.

  Lemma invariant_set_d1 : forall state d',
      TD.disk0 state = None ->
      invariant (TD.set_disk d1 state d').
  Proof.
    destruct state; cleanup.
  Qed.

  Opaque TD.set_disk.

  Hint Resolve invariant_d1.

  Lemma abstraction_is_some_disk : forall state,
      {TD.disk0 state = Some (D.sdisk (abstraction state))} +
      {TD.disk0 state = None /\
       TD.disk1 state = Some (D.sdisk (abstraction state))}.
  Proof.
    destruct state; cleanup.
    destruct disk0, disk1; cleanup;
      abstraction_simpl.
    exfalso.
    repeat deex; intuition congruence.
  Qed.

  Hint Resolve d0_upd_set_d0.

  Theorem TDWrite0_inbounds_ok : forall a b,
      prog_spec
        (fun b0 (state:TD.State) =>
           {|
             pre := invariant state /\
                    D.sdisk (abstraction state) a = Some b0;
             post :=
               fun r state' =>
                 (abstraction state' = D.Disk (diskUpd (D.sdisk (abstraction state)) a b) /\
                  d0_upd state' a b) \/
                 (abstraction state' = abstraction state /\
                  TD.disk0 state' = None);
             crash :=
               fun state' =>
                 (abstraction state' = abstraction state /\
                  invariant state') \/
                 (abstraction state' = D.Disk (diskUpd (D.sdisk (abstraction state)) a b) /\
                  (* this should be a recoverable property *)
                  d0_upd state' a b)
           |})
        (Prim (TD.Write d0 a b))
        TD.step.
  Proof.
    start_spec.
    TD.inv_step;
      subst_var;
      try abstraction_fwd;
      try inv_fwd.
    destruct (abstraction_is_some_disk x); cleanup.
    rewrite ?abstraction_set_d0 in *.
    intuition eauto.
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
    start_spec.
    TD.inv_step; subst_var;
      try abstraction_fwd;
      try inv_fwd.
    destruct i, (abstraction_is_some_disk x); cleanup.
    admit.
    destruct (TD.disk1 x) eqn:?; cleanup.
    admit.
  Admitted.

  Hint Resolve d0_upd_to_invariant.

  Lemma d0_upd_after_step : forall state state' a b,
      d0_upd state a b ->
      TD.bg_step state state' ->
      (d0_upd state' a b /\
       abstraction state' = abstraction state) \/
      (exists b0 d, TD.disk0 state' = None /\
               TD.disk1 state' = Some d /\
               d a = Some b0 /\
               abstraction state = D.Disk (diskUpd d a b)).
  Proof.
    inversion 2; cleanup; autorewrite with upd;
      erewrite ?diskUpd_eq_some by eauto;
      eauto 10.
  Qed.

  Ltac d0_upd_fwd :=
    match goal with
    | [ H: d0_upd ?state _ _,
           H': TD.bg_step ?state _ |- _ ] =>
      eapply d0_upd_after_step in H; eauto;
      hyp_intuition
    end.

  Lemma d0_upd_cases : forall state a b,
      d0_upd state a b ->
      TD.disk0 state = Some (D.sdisk (abstraction state)) /\
      (exists b0 d', TD.disk1 state = Some d' /\
                d' a = Some b0 /\
                D.sdisk (abstraction state) = diskUpd d' a b) \/
      TD.disk1 state = None.
  Proof.
    destruct state; cleanup.
    destruct disk0, disk1; cleanup.
    intuition eauto.
  Qed.

  Ltac d0_upd_split :=
    match goal with
    | [ H: d0_upd _ _ _ |- _ ] =>
      pose proof (d0_upd_cases _ _ _ H);
      hyp_intuition
    end.

  Hint Resolve invariant_d0.
  Hint Resolve invariant_set_d1.

  Theorem TDWrite1_inbounds_d0_ok : forall a b,
      prog_spec
        (fun (_:unit) (state:TD.State) =>
           {|
             pre := d0_upd state a b;
             post :=
               fun r state' =>
                 abstraction state' = abstraction state /\
                 invariant state';
             crash :=
               fun state' =>
                 (abstraction state' = abstraction state /\
                  d0_upd state' a b) \/
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
    start_spec.
    TD.inv_step;
      subst_var;
      cleanup.
    d0_upd_fwd.
    - d0_upd_split; cleanup.
      erewrite abstraction_set_d1_with_d0 by eauto; auto.
    - cleanup.
      erewrite abstraction_set_d1 by eauto; auto.
  Qed.

  Theorem TDWrite1_inbounds_no_d0_ok : forall a b,
      prog_spec
        (fun b0 (state:TD.State) =>
           {|
             pre := invariant state /\
                    TD.disk0 state = None /\
                    D.sdisk (abstraction state) a = Some b0;
             post :=
               fun r state' =>
                 abstraction state' = D.Disk (diskUpd (D.sdisk (abstraction state)) a b) /\
                 invariant state';
             crash :=
               fun state' =>
                 (abstraction state' = abstraction state /\
                  invariant state') \/
                 (abstraction state' = D.Disk (diskUpd (D.sdisk (abstraction state)) a b) /\
                 invariant state');
           |})
        (Prim (TD.Write d1 a b))
        TD.step.
  Proof.
    start_spec.
    TD.inv_step;
      subst_var;
      inv_fwd;
      cleanup.

    destruct (TD.disk1 state) eqn:?; cleanup.
    abstraction_simpl; cleanup.
    erewrite abstraction_set_d1 by eauto.
    abstraction_simpl.
    eauto.
  Qed.

  Theorem Write_inbounds_ok : forall a b,
      prog_spec
        (fun b0 state =>
           {|
             pre := invariant state /\
                    D.sdisk (abstraction state) a = Some b0;
             post :=
               fun r state' =>
                 abstraction state' = D.Disk (diskUpd (D.sdisk (abstraction state)) a b) /\
                 invariant state';
             crash :=
               fun state' =>
                 (abstraction state' = abstraction state /\
                  invariant state') \/
                 (abstraction state' = D.Disk (diskUpd (D.sdisk (abstraction state)) a b) /\
                  d0_upd state' a b) \/
                 (abstraction state' = D.Disk (diskUpd (D.sdisk (abstraction state)) a b) /\
                 invariant state');
           |})
        (Write a b)
        TD.step.
  Proof.
    start_spec.
    - eapply TDWrite0_inbounds_ok in H6; cleanup.
      intuition; rew_abstraction.
      + inv_exec; cleanup; eauto.
        eapply TDWrite1_inbounds_d0_ok in H9; cleanup;
          rew_abstraction;
          eauto.
        eapply TDWrite1_inbounds_d0_ok in H9; cleanup;
          rew_abstraction;
          eauto.

        eapply TDWrite1_inbounds_d0_ok in H9; cleanup;
          rew_abstraction;
          eauto.
      + inv_exec; cleanup; eauto.
        eapply TDWrite1_inbounds_no_d0_ok in H9; cleanup;
          rew_abstraction;
          eauto.
        eapply TDWrite1_inbounds_no_d0_ok in H9; cleanup;
          rew_abstraction;
          eauto.

        eapply TDWrite1_inbounds_no_d0_ok in H9; cleanup;
          rew_abstraction;
          intuition eauto.
    - eapply TDWrite0_inbounds_ok in H6; cleanup;
        rew_abstraction;
        intuition eauto.
  Qed.

  Theorem Write_oob_ok : forall a b,
      prog_spec
        (fun (_:unit) state =>
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
                 invariant state';
           |})
        (Write a b)
        TD.step.
  Proof.
    start_spec.
    - eapply TDWrite_oob_ok in H6; cleanup.
      inv_exec; cleanup; eauto.
      eapply TDWrite_oob_ok in H9; rew_abstraction; cleanup.
      eapply TDWrite_oob_ok in H9; rew_abstraction; cleanup.
      eapply TDWrite_oob_ok in H9; rew_abstraction; cleanup.
    - eapply TDWrite_oob_ok in H6; cleanup.
  Qed.

  Lemma step_write' : forall state a v b,
      D.step (D.Write a b) state v
             (D.Disk (diskUpd (D.sdisk state) a b)).
  Proof.
    destruct v; intros.
    eauto.
  Qed.

  Hint Resolve step_write'.

  Lemma step_write_oob : forall state a b v,
      D.sdisk state a = None ->
      D.step (D.Write a b) state v state.
  Proof.
    destruct v; intros.
    pose proof (D.step_write a b state).
    autorewrite with upd in *.
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
    - destruct op; simpl in *.
      + eapply Read_ok in H0; cleanup; rew_abstraction.
        intuition eauto.
      + destruct (D.sdisk (abstraction state) a) eqn:?.
        eapply Write_inbounds_ok in H0; cleanup; rew_abstraction;
          intuition eauto.

        eapply Write_oob_ok in H0; cleanup; rew_abstraction;
          intuition eauto.
    - destruct op; cleanup.
      + eapply Read_ok in H0; cleanup.
      + destruct (D.sdisk (abstraction state) a) eqn:?.
        eapply Write_inbounds_ok in H0; cleanup; rew_abstraction.
        hyp_intuition; rew_abstraction; eauto.
        intuition; eauto.
        admit. (* TODO: d0_upd state' requires recovery to achieve invariant *)

        eapply Write_oob_ok in H0; cleanup; rew_abstraction;
          intuition eauto.

    Grab Existential Variables.
    all: auto.
  Abort.

End RD.
