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

  (* TODO: this is slow, need to debug *)
  Ltac finish :=
    repeat match goal with
           | _ => solve_false
           | [ H: md_pred ?d _ _ |-
               md_pred ?d _ _ ] =>
             eapply md_pred_impl; [ apply H | cancel ]
           | _ => solve [ intuition eauto ]
           end.

  Ltac step :=
    step_prog; simplify; finish.

  Lemma md_pred_false : forall d, md_pred d [|False|] False -> False.
  Proof.
    destruct d; simpl; intros; eauto.
    apply lift_extract in H; auto.
  Qed.

  Hint Resolve md_pred_false.

  Theorem Read_ok : forall a,
      prog_spec
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
    intros; eapply prog_ok_to_spec; simplify; finish.

    step.
    descend; intuition eauto.

    destruct r; step.
    descend; intuition eauto; simplify.

    destruct r; step.
    (intuition eauto); finish.

    (intuition eauto); finish.
  Qed.

  Theorem Write_ok : forall a b,
      prog_spec
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
                  md_pred (TD.disk1 state') (F * a |-> b0) True) \/
                 (md_pred (TD.disk0 state') (F * a |-> b) True /\
                  md_pred (TD.disk1 state') (F * a |-> b) True);
           |})
        (Write a b)
        TD.step.
  Proof.
    unfold Write.
    intros; eapply prog_ok_to_spec; simplify; finish.

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

  Theorem TDRead0_oob_ok : forall a,
      prog_ok
        (fun F state =>
           {|
             pre := md_pred (TD.disk0 state) F True /\
                    md_pred (TD.disk1 state) F True /\
                    abstraction state a = None;
             post :=
               fun r state' =>
                 match r with
                 | Working v => md_pred (TD.disk0 state') F False /\
                               md_pred (TD.disk1 state') F True
                 | Failed => md_pred (TD.disk0 state') (lift False) True /\
                            md_pred (TD.disk1 state') F False
                 end;
             crash :=
               fun state' =>
                 md_pred (TD.disk0 state') F True /\
                 md_pred (TD.disk1 state') F True;
           |})
        (Prim (TD.Read d0 a))
        TD.step.
  Proof.
    start_prim.
    TD.inv_step.
    TD.inv_bg; simpl in *; subst; eauto.
    destruct state'.
    destruct disk0; simpl in *; repeat (simpl_match || deex || subst); eauto.
    destruct disk1; eauto.
    simpl_match; repeat deex; eauto.
  Qed.

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

  Lemma forall_tuple : forall A B {P: A*B -> Prop},
      (forall p, P p) ->
      (forall a b, P (a, b)).
  Proof.
    intuition.
  Qed.

  Ltac expand_forall :=
    match goal with
    | [ H: forall _:_ * _, _ |- _ ] =>
      let H' := fresh in
      pose proof (forall_tuple H) as H';
      clear H;
      rename H' into H;
      simpl in H
    end.

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

  Theorem RD_ok : interpretation
                    op_impl
                    TD.step D.step
                    invariant
                    abstraction.
  Proof.
    eapply interpret_exec; intros; eauto.
    - destruct op; simpl in *.
      + destruct (abstraction state a) eqn:?.
        pose proof (prog_spec_exec (@Read_ok a) H0).
        repeat expand_forall.
        (* TODO: factor out process of threading this particular frame
        through *)
        specialize (H1 (pred_except (mem_is (abstraction state)) a b) b).
        match type of H1 with
        | ?P -> _ => assert P
        end.
        eapply invariant_abstraction_pred; eauto.
        eapply mem_is_except; eauto.
        safe_intuition.
        pose proof (invariant_abstraction_pred' _ _ H4 H5).
        match goal with
        | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
          apply pred_except_ptsto in H;
            apply mem_is_extract in H;
            apply diskMem_ext_eq in H
        end.
        replace (abstraction state').
        intuition eauto.
        constructor; intros; congruence.
        eapply invariant_both_disks; intros.
        unfold md_pred in *; repeat simpl_match.
        repeat match goal with
               | [ H: _ |= pred_except _ ?a _ * ?a |-> _ |- _ ] =>
                 apply pred_except_ptsto in H;
                   apply mem_is_extract in H;
                   apply diskMem_ext_eq in H
               end.
        congruence.
        admit. (* TODO: need a spec for OOB reads *)
      + destruct (abstraction state a) eqn:?.
        pose proof (prog_spec_exec (@Write_ok a b) H0).
        repeat expand_forall.
        admit.
        admit. (* TODO: need a spec for OOB writes *)
    - destruct op in *; simpl in *.
      + destruct (abstraction state a) eqn:?.
        pose proof (prog_spec_exec (@Read_ok a) H0).
        repeat expand_forall.
        admit.
        admit. (* TODO: need a spec for OOB reads *)
      + destruct (abstraction state a) eqn:?.
        pose proof (prog_spec_exec (@Write_ok a b) H0).
        repeat expand_forall.
        (* can't prove invariant, need a weaker crash invariant for refinement,
         which should be chained to a recovery procedure *)
        admit.
        admit. (* TODO: need a spec for OOB writes *)
  Abort.

End RD.
