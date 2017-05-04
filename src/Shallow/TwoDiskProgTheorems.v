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

Arguments md_pred md F%pred P.

Theorem md_pred_weaken : forall md F (P P':Prop),
    md_pred md F P ->
    (P -> P') ->
    md_pred md F P'.
Proof.
  destruct md; intuition.
Qed.

Theorem md_pred_none : forall md F (P:Prop),
    P ->
    md = None ->
    md_pred md F P.
Proof.
  intros; subst; intuition.
Qed.

Theorem md_pred_impl : forall md F F' P,
    md_pred md F P ->
    (F ===> F') ->
    md_pred md F' P.
Proof.
  destruct md; simpl in *; intros; eauto.
Qed.

Theorem md_pred_some : forall md F (P:Prop) m,
    md = Some m ->
    md_pred md F P ->
    m |= F.
Proof.
  unfold md_pred; intros; simpl_match; auto.
Qed.

Hint Resolve md_pred_weaken md_pred_none.

Ltac start_prim :=
  intros; eapply prim_ok; intros;
  repeat destruct_tuple;
  simpl in *;
  safe_intuition;
  try solve [ intuition eauto ].

Theorem TDRead0_ok : forall a,
    prog_ok
      (fun '(F0, F1, v0) state =>
         {|
           pre := md_pred (TD.disk0 state) (F0 * a |-> v0) True /\
                  md_pred (TD.disk1 state) F1 True;
           post :=
             fun r state' =>
               match r with
               | Working v => v = v0 /\
                             md_pred (TD.disk0 state') (F0 * a |-> v0) False /\
                             md_pred (TD.disk1 state') F1 True
               | Failed => md_pred (TD.disk0 state') (lift False) True /\
                          md_pred (TD.disk1 state') F1 False
               end;
           crash :=
             fun state' =>
               md_pred (TD.disk0 state') (F0 * a |-> v0) True /\
               md_pred (TD.disk1 state') F1 True;
         |})
      (Prim (TD.Read d0 a))
      TD.step.
Proof.
  start_prim.
  TD.inv_step.
  TD.inv_bg; simpl in *; repeat simpl_match; eauto.
  - destruct (TD.disk0 state') eqn:?; simpl in *; subst.
    + pose proof (ptsto_valid H).
      unfold disk_get in *.
      simpl_match; subst; intuition eauto.
    + destruct state'; simpl in *; subst; intuition eauto.
      destruct disk1; simpl; intuition eauto.
  - pose proof (ptsto_valid H).
    unfold disk_get in *.
    simpl_match; subst; intuition eauto.
Qed.

Theorem TDRead1_ok : forall a,
    prog_ok
      (fun '(F0, F1, v0) state =>
         {|
           pre := md_pred (TD.disk0 state) F0 True /\
                  md_pred (TD.disk1 state) (F1 * a |-> v0) True;
           post :=
             fun r state' =>
               match r with
               | Working v => v = v0 /\
                             md_pred (TD.disk0 state') F0 True /\
                             md_pred (TD.disk1 state') (F1 * a |-> v0) False
               | Failed => md_pred (TD.disk0 state') F0 False /\
                          md_pred (TD.disk1 state') (lift False) True
               end;
           crash :=
             fun state' =>
               md_pred (TD.disk0 state') F0 True /\
               md_pred (TD.disk1 state') (F1 * a |-> v0) True;
         |})
      (Prim (TD.Read d1 a))
      TD.step.
Proof.
  start_prim.
  TD.inv_step.
  TD.inv_bg; simpl in *; repeat simpl_match; eauto.
  destruct (TD.disk1 state') eqn:?; simpl in *; subst.
  pose proof (ptsto_valid H1).
  unfold disk_get in *.
  simpl_match; subst; intuition eauto.
  destruct state'; simpl in *; subst; intuition eauto.
  destruct disk0; simpl; intuition eauto.
  pose proof (ptsto_valid H1).
  unfold disk_get in *.
  simpl_match; subst; intuition eauto.
Qed.

Hint Resolve ptsto_diskUpd.

Theorem TDWrite0_ok : forall a b,
    prog_ok
      (fun '(F0, F1, v0) state =>
         {|
           pre := md_pred (TD.disk0 state) (F0 * a |-> v0) True /\
                  md_pred (TD.disk1 state) F1 True;
           post :=
             fun r state' =>
               match r with
               | Working _ => md_pred (TD.disk0 state') (F0 * a |-> b) False /\
                             md_pred (TD.disk1 state') F1 True
               | Failed => md_pred (TD.disk0 state') (lift False) True /\
                          md_pred (TD.disk1 state') F1 False
               end;
           crash :=
             fun state' =>
               md_pred (TD.disk0 state') (F0 * a |-> v0) True /\
               md_pred (TD.disk1 state') F1 True;
         |})
      (Prim (TD.Write d0 a b))
      TD.step.
Proof.
  start_prim.
  TD.inv_step; simpl.
  TD.inv_bg; simpl in *; intuition (subst; eauto).
  destruct matches in *; simpl in *; intuition (subst; simpl; eauto);
    try congruence.
  destruct (TD.disk1 x) eqn:?; simpl; eauto.
  destruct x; eauto.
  destruct (d_0 a); intuition (subst; simpl; eauto).
Qed.

Theorem TDWrite1_ok : forall a b,
    prog_ok
      (fun '(F0, F1, v0) state =>
         {|
           pre := md_pred (TD.disk0 state) F0 True /\
                  md_pred (TD.disk1 state) (F1 * a |-> v0) True;
           post :=
             fun r state' =>
               match r with
               | Working _ => md_pred (TD.disk0 state') F0 True /\
                             md_pred (TD.disk1 state') (F1 * a |-> b) False
               | Failed => md_pred (TD.disk0 state') F0 False /\
                          md_pred (TD.disk1 state') (lift False) True
               end;
           crash :=
             fun state' =>
               md_pred (TD.disk0 state') F0 True /\
               md_pred (TD.disk1 state') (F1 * a |-> v0) True;
         |})
      (Prim (TD.Write d1 a b))
      TD.step.
Proof.
  start_prim.
  TD.inv_step; simpl.
  TD.inv_bg; simpl in *; intuition (subst; eauto).
  destruct matches in *; simpl in *; intuition (subst; simpl; eauto);
    try congruence.
  destruct (TD.disk0 x) eqn:?; simpl; eauto.
  destruct x; eauto.
  destruct (d_1 a); intuition (subst; simpl; eauto).
Qed.

Hint Extern 1 {{ Prim (TD.Read d0 _); _}} => apply TDRead0_ok : prog.
Hint Extern 1 {{ Prim (TD.Read d1 _); _}} => apply TDRead1_ok : prog.
Hint Extern 1 {{ Prim (TD.Write d0 _ _); _}} => apply TDWrite0_ok : prog.
Hint Extern 1 {{ Prim (TD.Write d1 _ _); _}} => apply TDWrite1_ok : prog.
