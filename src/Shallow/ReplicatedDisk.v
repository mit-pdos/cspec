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

  (* TODO: currently this just re-states the D.step semantics in a functional
  rather than inductive way; want to make it based on separation logic *)
  Definition sl_spec : Semantics D.Op D.State :=
    fun T op state =>
      match op with
      | D.Read a =>
        match state a with
        | Some v0 => fun v state' => v = v0 /\ state' = state
        | None => fun v state' => state' = state
        end
      | D.Write a b =>
        fun v state' => state' = diskUpd state a b
      end.

  Theorem sl_spec_ok : semantics_impl sl_spec D.step.
  Proof.
    unfold semantics_impl, sl_spec; intros.
    destruct matches in *; intuition (subst; eauto).
    constructor; intros; congruence.
    constructor; intros; congruence.
    destruct v.
    constructor.
  Qed.

  Theorem RD_ok : interpretation
                    op_impl
                    TD.step D.step
                    invariant
                    abstraction.
  Proof.
    apply interpretation_weaken with sl_spec.
    apply sl_spec_ok.
    eapply interpret_exec; intros; eauto.
    - destruct op; simpl in *.
      + destruct (abstraction state a) eqn:?.
        pose proof (prog_spec_exec (@Read_ok a) H0).
        repeat expand_forall.
        admit.
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
