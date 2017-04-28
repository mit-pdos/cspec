Require Import FunctionalExtensionality.

Require Import Disk.
Require Import Automation.

Require Import Shallow.ProgLang.Prog.
Require Import Shallow.TwoDiskProg.
Require Import Shallow.SeqDiskProg.

Require Import Interpret.

Module RD.

  Definition Read (a:addr) : TD.prog block :=
    mv0 <- Prim (TD.Read d0 a);
      match mv0 with
      | Working v => Ret v
      | Failed => mv2 <- Prim (TD.Read d0 a);
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
      forall a, match d_0 a with
           | Some v0 => d_1 a = Some v0
           | None => d_1 a = None
           end
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
    inversion 2; subst; simpl in *; eauto.
    repeat deex.
    f_equal.
    extensionality a.
    specialize (H a).
    destruct matches in *; eauto.
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

  Theorem RD_ok : interpretation
                    op_impl
                    TD.step D.step
                    invariant
                    abstraction.
  Proof.
    eapply interpret_exec; intros; eauto.
    - destruct op; simpl in *; unfold Read, Write in *.
      + inv_exec.
        destruct v0; safe_intuition.
        inv_exec.
        match goal with
        | [ H: TD.step _ _ _ _ |- _ ] =>
          inversion H; safe_intuition; eauto
        end.
        match goal with
        | [ H: TD.op_step _ _ _ _ |- _ ] =>
          inversion H; safe_intuition; eauto;
            repeat sigT_eq
        end.
        intuition eauto.
        rewrite <- (@abstraction_preserved_bg_step state state'); eauto.
        destruct matches in *.
        match goal with
        | [ H: Working _ = Working _ |- _ ] =>
          inversion H; subst
        end.
        econstructor; eauto.
        erewrite abstraction_d0_eq; eauto; simpl; eauto.
        econstructor; eauto.
        erewrite abstraction_d0_eq; eauto; simpl; eauto.

        (* need to read second disk *)
        inv_exec.
        admit.
      + inv_exec.
        match goal with
        | [ H: TD.step _ _ _ _ |- _ ] =>
          inversion H; safe_intuition; eauto
        end.
        match goal with
        | [ H: TD.op_step _ _ _ _ |- _ ] =>
          inversion H; safe_intuition; eauto;
            repeat sigT_eq
        end.
        subst state'1 r.
        inv_exec.
        destruct (TD.get_disk d0 x).
        destruct (d a).

        unfold TD.step, background_step in *;
          repeat deex.
        (* TODO: really need specs to make these cases manageable; they don't
        require much work but manipulating hypotheses is quite painful *)
        admit.
        admit.
        admit.
    - (* also need crash proofs *)
  Abort.

End RD.
