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

  Ltac step :=
    step_prog;
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
           end;
    try solve [ (intuition eauto);
                try solve_false ].

  Ltac cancel :=
    match goal with
    | [ |- lift ?P ===> _ ] =>
      lazymatch P with
      | True => fail
      | _ => apply lift1_left; intro; try congruence; try contradiction
      end
    end.

  Lemma md_pred_false : forall d, md_pred d [|False|] False -> False.
  Proof.
    destruct d; simpl; intros; eauto.
    apply lift_extract in H; auto.
  Qed.

  Hint Resolve md_pred_false.

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
                 md_pred (TD.disk0 state) (F * a |-> b0) True /\
                 md_pred (TD.disk1 state) (F * a |-> b0) True;
           |})
        (Read a)
        TD.step.
  Proof.
    unfold Read.
    step.
    descend; intuition eauto.

    destruct r; step.
    descend; intuition eauto.

    destruct r; step.
    intuition eauto.

    eapply md_pred_impl; eauto.
    cancel.
  Qed.

  Theorem Write_ok : forall a b,
      prog_ok
        (fun '(F, b0) state =>
           {|
             pre := md_pred (TD.disk0 state) (F * a |-> b0) True /\
                    md_pred (TD.disk1 state) (F * a |-> b0) True;
             post :=
               fun r state' =>
                 r = tt /\
                 md_pred (TD.disk0 state') (F * a |-> b) True /\
                 md_pred (TD.disk1 state') (F * a |-> b) True;
             crash :=
               fun state' =>
                 md_pred (TD.disk0 state) (F * a |-> b0) True /\
                 md_pred (TD.disk1 state) (F * a |-> b0) True;
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

    descend; intuition eauto.
    destruct r; step.
    intuition eauto.
    eapply md_pred_impl; eauto.
    cancel.
  Qed.

  Theorem RD_ok : interpretation
                    op_impl
                    TD.step D.step
                    invariant
                    abstraction.
  Proof.
    eapply interpret_exec; intros; eauto.
    - destruct op; simpl in *.
      + admit.
      + admit.
    - destruct op in *; simpl in *.
      + admit.
      + admit.
  Abort.

End RD.
