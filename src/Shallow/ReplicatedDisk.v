Require Import FunctionalExtensionality.

Require Import Disk.
Require Import Automation.

Require Import Shallow.ProgLang.Prog.
Require Import Shallow.ProgLang.Hoare.
Require Import Shallow.TwoDiskProg.
Require Import Shallow.TwoDiskProg Shallow.TwoDiskProgTheorems.
Require Import Shallow.SeqDiskProg.

Require Import SepLogic.Pred.
Require Import Interpret.

(* TODO: why is opacity not preserved from imports? *)
Opaque star ptsto pred_prop.

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

  (* Recovery tracks what happens at each step in order to implement control
  flow. *)
  Inductive RecStatus :=
  (* continue working, nothing interesting has happened *)
  | Continue
  (* some address has been repaired (or the recovery has exhausted the
  addresses) - only one address can be out of sync and thus only it must be
  recovered. *)
  | RepairDone
  (* one of the disks has failed, so don't bother continuing recovery since the
  invariant is now trivially satisfied *)
  | DiskFailed (i:diskId).

  Definition fixup (a:addr) : TD.prog RecStatus :=
    mv0 <- Prim (TD.Read d0 a);
      match mv0 with
      | Working v => mv2 <- Prim (TD.Read d1 a);
                      match mv2 with
                      | Working v' => if v == v' then
                                       Ret Continue
                                     else
                                       mu <- Prim (TD.Write d1 a v);
                                       Ret (match mu with
                                            | Working _ => RepairDone
                                            | Failed => DiskFailed d1
                                            end)
                      | Failed => Ret (DiskFailed d1)
                      end
      | Failed => Ret (DiskFailed d0)
      end.

  (* recursively performs recovery at [a-1], [a-2], down to 0 *)
  Fixpoint recover_at (a:addr) : TD.prog RecStatus :=
    match a with
    | 0 => Ret RepairDone
    | S n => s <- fixup n;
              match s with
              | Continue => recover_at n
              | RepairDone => Ret RepairDone
              | DiskFailed i => Ret (DiskFailed i)
              end
    end.

  (* recovery for a disk of size [sz] *)
  Definition Recover (sz:nat) : TD.prog unit :=
    _ <- recover_at sz;
      Ret tt.

  Definition op_impl T (op:D.Op T) : TD.prog T :=
    match op with
    | D.Read a => Read a
    | D.Write a b => Write a b
    end.

  Definition interpret := Interpret.interpret op_impl.

  Definition abstraction (state:TD.State) : D.State :=
    match state with
    | TD.Disks (Some d) _ _ => d
    | TD.Disks None (Some d) _ => d
    | _ => empty_disk (* impossible *)
    end.

  Definition invariant (state:TD.State) :=
    match state with
    | TD.Disks (Some d_0) (Some d_1) _ =>
      d_0 = d_1
    | _ => True
    end.

  Definition crash_invariant (state:TD.State) :=
    match state with
    | TD.Disks (Some d_0) (Some d_1) _ =>
      d_0 = d_1 \/
      exists a b0 b1,
        d_1 a = Some b1 /\
        diskMem d_0 = upd d_1 a b0
    | _ => True
    end.

  Theorem crash_invariant_weakens_invariant : forall state,
      invariant state -> crash_invariant state.
  Proof.
    unfold invariant, crash_invariant; intros.
    destruct matches; intuition eauto.
  Qed.

  Lemma exists_tuple2 : forall A B (P: A * B -> Prop),
      (exists a b, P (a, b)) ->
      (exists p, P p).
  Proof.
    intros.
    repeat deex; eauto.
  Qed.

  Ltac simplify :=
    repeat match goal with
           | |- forall _, _ => intros
           | _ => deex
           | _ => destruct_tuple
           | |- _ /\ _ => split; [ solve [auto] | ]
           | |- _ /\ _ => split; [ | solve [auto] ]
           (* TODO: extract the match pattern inside the exists on a0 and use
              those names in exists_tuple *)
           | |- exists (_: _*_), _ => apply exists_tuple2
           | _ => progress simpl in *
           | _ => progress safe_intuition
           | _ => progress subst
           | [ crashinv: _ -> Prop |- _ ] =>
             match goal with
             | [ H: forall _, _ -> crashinv _ |-
                 crashinv _ ] =>
               eapply H
             end
           end.

  Ltac cancel :=
    match goal with
    | [ |- lift ?P ===> _ ] =>
      lazymatch P with
      | True => fail
      | _ => apply lift1_left; intro; try congruence; try contradiction
      end
    end.

  Ltac finish :=
    repeat match goal with
           | [ H: md_pred ?d _ _ |-
               md_pred ?d _ _ ] =>
             eapply md_pred_impl; [ apply H | cancel ]
           | _ => solve_false
           | _ => solve [ intuition eauto ]
           end.

  Ltac step :=
    step_prog; simplify; finish.

  Lemma md_pred_false : forall d, md_pred d [|False|] False -> False.
  Proof.
    destruct d; simpl; intros; eauto.
    apply lift_extract in H; auto.
  Qed.

  Hint Extern 1 False => match goal with
                    | [ H: md_pred ?d [|False|] False |- _ ] =>
                      apply (md_pred_false d H)
                    end : false.

  Theorem Read_ok : forall a,
      prog_ok
        (fun '(F, b0) state =>
           {|
             pre := md_pred (TD.disk0 state) (F * a |-> b0) True /\
                    md_pred (TD.disk1 state) (F * a |-> b0) True;
             post :=
               fun r state' =>
                 r = b0 /\
                 md_pred (TD.disk0 state') (F * a |-> b0) True /\
                 md_pred (TD.disk1 state') (F * a |-> b0) True;
             crash :=
               fun state' =>
                 md_pred (TD.disk0 state') (F * a |-> b0) True /\
                 md_pred (TD.disk1 state') (F * a |-> b0) True;
           |})
        (Read a)
        TD.step.
  Proof.
    unfold Read.

    step.
    descend; intuition eauto.

    destruct r; step.
    descend; intuition eauto; simplify.

    destruct r; step.
    (intuition eauto); finish.

    (intuition eauto); finish.
  Qed.

  Theorem Write_ok : forall a b,
      prog_ok
        (fun '(F, b0) state =>
           {|
             pre :=
               md_pred (TD.disk0 state) (F * a |-> b0) True /\
               md_pred (TD.disk1 state) (F * a |-> b0) True;
             post :=
               fun r state' =>
                 r = tt /\
                 md_pred (TD.disk0 state') (F * a |-> b) True /\
                 md_pred (TD.disk1 state') (F * a |-> b) True;
             crash :=
               fun state' =>
                 (md_pred (TD.disk0 state') (F * a |-> b0) True /\
                  md_pred (TD.disk1 state') (F * a |-> b0) True) \/
                 (md_pred (TD.disk0 state') (F * a |-> b) True /\
                  md_pred (TD.disk1 state') (F * a |-> b0) True);
           |})
        (Write a b)
        TD.step.
  Proof.
    unfold Write.

    step.
    descend; intuition eauto.
    destruct r; step.
    descend; intuition eauto.

    step.
    destruct r; intuition eauto.
    eapply md_pred_impl; eauto.
    cancel.

    descend; intuition eauto; simplify.
    destruct r; step.
    intuition eauto.
    finish.

    left; intuition eauto.
    finish.
  Qed.

  Theorem fixup_correct_addr_ok : forall a,
      prog_ok
        (fun '(F, b, b') state =>
           {|
             pre :=
               md_pred (TD.disk0 state) (F * a |-> b') True /\
               md_pred (TD.disk1 state) (F * a |-> b) True;
             post :=
               fun r state' =>
                match r with
                | Continue => b = b'
                | RepairDone =>
                  md_pred (TD.disk0 state') (F * a |-> b') True /\
                  md_pred (TD.disk1 state') (F * a |-> b') True
                | DiskFailed i =>
                  match i with
                  | d0 => md_pred (TD.disk0 state') (F * a |-> b) True /\
                         md_pred (TD.disk1 state') (F * a |-> b) False
                  | d1 => md_pred (TD.disk0 state') (F * a |-> b') False /\
                         md_pred (TD.disk1 state') (F * a |-> b') True
                  end
                end;
             crash :=
               fun state' =>
               md_pred (TD.disk0 state) (F * a |-> b') True /\
               md_pred (TD.disk1 state) (F * a |-> b) True;
           |})
        (fixup a)
        TD.step.
  Proof.
    unfold fixup; intros.
    step.
    descend; intuition eauto.

    destruct r; try step.
    descend; intuition eauto.

    destruct r; try step.
    is_eq b' v; try step.
    descend; intuition eauto.

    step.
    destruct r; intuition eauto; simplify; finish.
  Qed.

  Lemma invariant_abstraction_pred : forall state F,
      invariant state ->
      abstraction state |= F ->
      md_pred (TD.disk0 state) F True /\
      md_pred (TD.disk1 state) F True.
  Proof.
    destruct state; simpl; intros.
    destruct disk0, disk1; simpl; subst; intuition.
  Qed.

  Lemma invariant_abstraction_pred' : forall state F,
      md_pred (TD.disk0 state) F True ->
      md_pred (TD.disk1 state) F True ->
      abstraction state |= F.
  Proof.
    destruct state; simpl; intros.
    destruct disk0, disk1; simpl; subst; intuition.
  Qed.

  (* for the invariant, it is sufficient to consider only states where both
  disks are present *)
  Lemma invariant_both_disks : forall state,
      (forall d d', TD.disk0 state = Some d ->
               TD.disk1 state = Some d' ->
               d = d') ->
      invariant state.
  Proof.
    destruct state; simpl in *; intros; eauto.
    destruct disk0, disk1; eauto.
  Qed.

  (* same for crash invariant: only interesting when both disks are present *)
  Lemma crash_invariant_both_disks : forall state,
      (forall d d', TD.disk0 state = Some d ->
               TD.disk1 state = Some d' ->
               d = d' \/
               exists a b0 b, d' a = Some b0 /\
                         diskMem d = upd d' a b) ->
      crash_invariant state.
  Proof.
    destruct state; simpl in *; intros; eauto.
    destruct disk0, disk1; eauto.
    specialize (H d d0); intuition.
    repeat deex; eauto 10.
  Qed.

  Hint Resolve mem_is_except.

  Lemma pred_except_combine : forall d d' a v,
      diskMem d |= pred_except (mem_is (diskMem d')) a v * a |-> v ->
      d = d'.
  Proof.
    intros.
    apply pred_except_ptsto in H.
    apply mem_is_extract in H.
    apply diskMem_ext_eq in H.
    assumption.
  Qed.

  Theorem Read_abstraction_ok : forall a,
      prog_spec
        (fun b0 state =>
           {|
             pre := invariant state /\
                    abstraction state a = Some b0;
             post :=
               fun r state' =>
                 r = b0 /\
                 invariant state' /\
                 abstraction state' = abstraction state;
             crash :=
               fun state' =>
                 invariant state' /\
                 abstraction state' = abstraction state;
           |})
        (Read a)
        TD.step.
  Proof.
    intros.
    eapply prog_ok_to_spec; simplify; finish.

    step_prog_with ltac:(apply Read_ok); simplify; finish.
    rename a0 into b0.
    exists (pred_except (mem_is (abstraction state)) a b0), b0.
    split; [ | split ].
    - eapply invariant_abstraction_pred; eauto.
    - step.
      intuition.
      eapply invariant_both_disks; simplify.
      repeat match goal with
             | [ H: md_pred ?d _ _, H': ?d = Some _ |- _ ] =>
               apply (md_pred_some _ _ H') in H
             end.
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_combine in H; subst
             end; auto.
      pose proof (invariant_abstraction_pred' _ _ H6 H7).
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_combine in H; subst
             end; auto.
    - simplify.
      intuition.
      eapply invariant_both_disks; simplify.
      repeat match goal with
             | [ H: md_pred ?d _ _, H': ?d = Some _ |- _ ] =>
               apply (md_pred_some _ _ H') in H
             end.
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_combine in H; subst
             end; auto.
      pose proof (invariant_abstraction_pred' _ _ H3 H4).
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_combine in H; subst
             end; auto.
  Qed.

  Lemma pred_except_upd_combine : forall (d d':disk) a v v',
      d' a = Some v ->
      diskMem d |= pred_except (mem_is (diskMem d')) a v * a |-> v' ->
      d = diskUpd d' a v'.
  Proof.
    intros.
    eapply pimpl_apply in H0; [ | rewrite mem_is_upd; reflexivity ].
    apply pred_except_ptsto in H0.
    apply mem_is_extract in H0.
    eapply diskMem_ext_eq.
    erewrite diskUpd_diskMem_commute; eauto.
  Qed.

  Hint Resolve crash_invariant_weakens_invariant.

  Lemma abstraction_satisfies_some_pred : forall state F F' (P P':Prop),
      md_pred (TD.disk0 state) F P ->
      md_pred (TD.disk1 state) F' P' ->
      abstraction state |= F \/
      abstraction state |= F' /\ P.
  Proof.
    intros.
    destruct state.
    destruct disk0, disk1; simpl in *; eauto.
    exfalso; eauto.
  Qed.

  Lemma forall_tuple : forall A B {P: A*B -> Prop},
      (forall p, P p) ->
      (forall a b, P (a, b)).
  Proof.
    intuition.
  Qed.

  Ltac forall_tuple :=
    match goal with
    | [ H: forall _:_ * _, _ |- _ ] =>
      let H' := fresh in
      pose proof (forall_tuple H) as H';
      clear H;
      rename H' into H;
      simpl in H
    end.

  Theorem Write_abstraction_ok : forall a b,
      prog_spec
        (fun b0 state =>
           {|
             pre := invariant state /\
                    abstraction state a = Some b0;
             post :=
               fun r state' =>
                 r = tt /\
                 invariant state' /\
                 abstraction state' = diskUpd (abstraction state) a b;
             crash :=
               fun state' =>
                 crash_invariant state' /\
                 (abstraction state' = abstraction state \/
                 abstraction state' = diskUpd (abstraction state) a b);
           |})
        (Write a b)
        TD.step.
  Proof.
    intros.
    eapply prog_ok_to_spec; simplify; finish.
    step_prog_with ltac:(apply Write_ok); simplify.
    rename a0 into b0.
    exists (pred_except (mem_is (abstraction state)) a b0), b0.
    split; [ | split ].
    - eapply invariant_abstraction_pred; eauto.
    - step.
      intuition.
      eapply invariant_both_disks; simplify.
      repeat match goal with
             | [ H: md_pred ?d _ _, H': ?d = Some _ |- _ ] =>
               apply (md_pred_some _ _ H') in H
             end.
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_upd_combine in H; auto; subst
             end; auto.
      pose proof (invariant_abstraction_pred' _ _ H6 H7).
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_upd_combine in H; auto; subst
             end; auto.
    - simplify.
      intuition.
      apply crash_invariant_weakens_invariant.
      eapply invariant_both_disks; simplify.
      repeat match goal with
             | [ H: md_pred ?d _ _, H': ?d = Some _ |- _ ] =>
               apply (md_pred_some _ _ H') in H
             end.
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_combine in H; subst
             end; auto.
      pose proof (invariant_abstraction_pred' _ _ H3 H5).
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_combine in H; subst
             end; auto.

      (* the interesting case: we're going to prove the upd case in the crash
      invariant *)
      eapply crash_invariant_both_disks; simplify.
      repeat match goal with
             | [ H: md_pred ?d _ _, H': ?d = Some _ |- _ ] =>
               apply (md_pred_some _ _ H') in H
             end.
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_combine in H; subst
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_upd_combine in H; auto; subst
             end; auto.
      right; descend; intuition eauto.
      (* maybe the invariant should just use diskUpd *)
      eapply diskUpd_diskMem_commute; eauto.

      pose proof (abstraction_satisfies_some_pred _ _ _ _ _ H3 H5).
      intuition;
      repeat match goal with
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_combine in H; subst
             | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
               apply pred_except_upd_combine in H; auto; subst
             end; eauto.
  Qed.

  Lemma read_step : forall a (state state':D.State) b,
      state a = Some b ->
      state' = state ->
      D.step (D.Read a) state b state'.
  Proof.
    intros; subst.
    constructor; auto.
  Qed.

  Lemma write_step : forall a b (state state':D.State) b0 u,
      state a = Some b0 ->
      state' = diskUpd state a b ->
      D.step (D.Write a b) state u state'.
  Proof.
    intros; subst.
    destruct u.
    econstructor; eauto.
  Qed.

  Hint Resolve read_step write_step.
  Hint Resolve tt.

  Theorem prog_spec_exec : forall `(spec: Specification A T State) `(p: prog opT T)
                             `(step: Semantics opT State),
      prog_spec spec p step ->
      forall state r, exec step p state r ->
             forall a, pre (spec a state) ->
                  match r with
                  | Finished v state' => post (spec a state) v state'
                  | Crashed state' => crash (spec a state) state'
                  end.
  Proof.
    unfold prog_spec; intros.
    eapply H; eauto.
  Qed.

  Theorem RD_ok : interpretation
                    op_impl
                    TD.step D.step
                    invariant crash_invariant
                    abstraction.
  Proof.
    eapply interpret_exec; intros; eauto.
    - destruct op; simpl in *.
      + destruct (abstraction state a) eqn:?.
        pose proof (prog_spec_exec (@Read_abstraction_ok a) H0).
        specialize (H1 b); simplify; finish.
        admit. (* TODO: deal with OOB reads *)
      + destruct (abstraction state a) eqn:?.
        pose proof (prog_spec_exec (@Write_abstraction_ok a b) H0).
        specialize (H1 b0); simplify; finish.
        admit. (* TODO: need a spec for OOB writes *)
    - destruct op in *; simpl in *.
      + destruct (abstraction state a) eqn:?.
        pose proof (prog_spec_exec (@Read_abstraction_ok a) H0).
        specialize (H1 b); simplify; finish.
        admit. (* TODO: need a spec for OOB reads *)
      + destruct (abstraction state a) eqn:?.
        pose proof (prog_spec_exec (@Write_abstraction_ok a b) H0).
        specialize (H1 b0); simplify; finish.
        admit. (* TODO: need a spec for OOB writes *)

        Grab Existential Variables.
        all: auto.
  Abort.

End RD.
