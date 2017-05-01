Require Import SepLogic.
Require Import Automation.
Require Import Disk.

Require Import Shallow.ProgLang.Hoare.
Require Import Shallow.ProgLang.Prog.
Require Import TwoDiskProg.

Opaque pred_prop.

Definition md_pred (md: option disk) (F: dpred) (P: Prop) :=
  match md with
  | Some d => d |= F
  | None => P
  end.

Theorem md_pred_weaken : forall md F (P P':Prop),
    md_pred md F P ->
    (P -> P') ->
    md_pred md F P'.
Proof.
  destruct md; intuition.
Qed.

Hint Resolve md_pred_weaken.

Theorem Read0_ok : forall a,
    prog_spec
      (fun '(F0, F1, v0) state =>
         {|
           pre := md_pred (TD.disk0 state) (F0 * a |-> v0)%pred True /\
                  md_pred (TD.disk1 state) F1 True;
           post :=
             fun r state' =>
               match r with
               | Working v => v = v0 /\
                             md_pred (TD.disk0 state') (F0 * a |-> v0)%pred False /\
                             md_pred (TD.disk1 state') F1 True
               | Failed => md_pred (TD.disk0 state') (lift False) True /\
                          md_pred (TD.disk1 state') F1 False
               end;
           crash :=
             fun state' =>
               md_pred (TD.disk0 state') (F0 * a |-> v0)%pred True /\
               md_pred (TD.disk1 state') F1 True;
         |})
      (Prim (TD.Read d0 a))
      TD.step.
Proof.
  unfold prog_spec; intros;
    repeat match goal with
           | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
             let a := fresh a in
             let b := fresh b in
             destruct p as [a b]
           end;
    simpl in *;
    safe_intuition.
  eapply (inversion_prim_exec H0); intros; eauto.
  TD.inv_step.
  inversion H2; subst; clear H2; simpl in *; repeat simpl_match; eauto.
  destruct (TD.disk0 state') eqn:?; simpl in *; subst.
  pose proof (ptsto_valid H).
  unfold disk_get in *.
  simpl_match; subst; intuition eauto.
  destruct state'; simpl in *; subst; intuition eauto.
  destruct disk1; simpl; intuition eauto.
  pose proof (ptsto_valid H).
  unfold disk_get in *.
  simpl_match; subst; intuition eauto.
  destruct v; subst; intuition eauto.
  destruct (TD.disk0 state'); simpl in *; eauto.
  apply lift_extract in H4; contradiction.
Qed.

Theorem Read1_ok : forall a,
    prog_spec
      (fun '(F0, F1, v0) state =>
         {|
           pre := md_pred (TD.disk0 state) F0 True /\
                  md_pred (TD.disk1 state) (F1 * a |-> v0)%pred True;
           post :=
             fun r state' =>
               match r with
               | Working v => v = v0 /\
                             md_pred (TD.disk0 state') F0 True /\
                             md_pred (TD.disk1 state') (F1 * a |-> v0)%pred False
               | Failed => md_pred (TD.disk0 state') F0 False /\
                          md_pred (TD.disk1 state') (lift False) True
               end;
           crash :=
             fun state' =>
               md_pred (TD.disk0 state') F0 True /\
               md_pred (TD.disk1 state') (F1 * a |-> v0)%pred True;
         |})
      (Prim (TD.Read d1 a))
      TD.step.
Proof.
  unfold prog_spec; intros;
    repeat match goal with
           | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
             let a := fresh a in
             let b := fresh b in
             destruct p as [a b]
           end;
    simpl in *;
    safe_intuition.
  eapply (inversion_prim_exec H0); intros; eauto.
  TD.inv_step.
  inversion H2; subst; clear H2; simpl in *; repeat simpl_match; eauto.
  destruct (TD.disk1 state') eqn:?; simpl in *; subst.
  pose proof (ptsto_valid H1).
  unfold disk_get in *.
  simpl_match; subst; intuition eauto.
  destruct state'; simpl in *; subst; intuition eauto.
  destruct disk0; simpl; intuition eauto.
  pose proof (ptsto_valid H1).
  unfold disk_get in *.
  simpl_match; subst; intuition eauto.
  destruct v; subst; intuition eauto.
  destruct (TD.disk1 state'); simpl in *; eauto.
  apply lift_extract in H5; contradiction.
Qed.
