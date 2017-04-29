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
    exact (D.SDisk d).
    destruct disk1.
    exact (D.SDisk d).
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
        (* TODO: prove and use Write specs *)
        admit.
    - (* also need crash proofs *)
  Abort.

End RD.
