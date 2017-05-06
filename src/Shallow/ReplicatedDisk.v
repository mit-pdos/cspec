Require Import FunctionalExtensionality.

Require Import Disk.
Require Import Automation.

Require Import Shallow.ProgLang.Prog.
Require Import Shallow.ProgLang.Hoare Shallow.ProgLang.HoareRecovery.
Require Import Shallow.TwoDiskProg.
Require Import Shallow.TwoDiskProg Shallow.TwoDiskProgTheorems.
Require Import Shallow.SeqDiskProg.

Require Import MaybeHolds.
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
           | |- _ /\ _ => split; [ solve [auto] | ]
           | |- _ /\ _ => split; [ | solve [auto] ]
           (* TODO: extract the match pattern inside the exists on a0 and use
              those names in exists_tuple *)
           | |- exists (_: _*_), _ => apply exists_tuple2
           | _ => progress simpl in *
           | _ => progress safe_intuition
           | _ => progress subst
           | _ => autorewrite with upd in *
           | [ crashinv: _ -> Prop |- _ ] =>
             match goal with
             | [ H: forall _, _ -> crashinv _ |-
                 crashinv _ ] =>
               eapply H
             end
           end.

  Ltac finish :=
    repeat match goal with
           | _ => solve_false
           | _ => solve [ intuition eauto ]
           end.

  Ltac step :=
    step_prog; simplify; finish.

  Hint Resolve pred_false.

  Lemma both_disks_not_false : forall state,
      TD.disk0 state |= [|False|] ->
      TD.disk1 state |= [|False|] ->
      False.
  Proof.
    destruct state; simpl; intros.
    destruct disk0, disk1; simpl in *; eauto.
  Qed.

  Hint Resolve both_disks_not_false : false.

  Theorem Read_ok : forall a,
      prog_ok
        (fun d state =>
           {|
             pre := TD.disk0 state |= eq d /\
                    TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                 d a |= eq r /\
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
             crash :=
               fun state' =>
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
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
  Qed.

  Theorem Write_ok : forall a b,
      prog_ok
        (fun d state =>
           {|
             pre :=
               TD.disk0 state |= eq d /\
               TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                 r = tt /\
                 TD.disk0 state' |= eq (diskUpd d a b) /\
                 TD.disk1 state' |= eq (diskUpd d a b);
             crash :=
               fun state' =>
                 (TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d) \/
                 (TD.disk0 state' |= eq (diskUpd d a b) /\
                  TD.disk1 state' |= eq d);
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

    descend; intuition eauto; simplify.
    destruct r; step.
  Qed.

  Lemma if_lt_dec : forall A n m (a a':A),
      n < m ->
      (if lt_dec n m then a else a') = a.
  Proof.
    intros.
    destruct (lt_dec n m); auto.
    contradiction.
  Qed.

  Lemma disks_eq_inbounds : forall d a v v',
      a < size d ->
      d a |= eq v ->
      d a |= eq v' ->
      v = v'.
  Proof.
    unfold disk_get; intros.
    pose proof (diskMem_domain d a).
    rewrite if_lt_dec in H2 by auto.
    repeat deex.
    rewrite H2 in H0.
    replace (d a) in *; simpl in *; subst; auto.
  Qed.

  (* we will show that fixup does nothing once the disks are the same *)
  Theorem fixup_equal_ok : forall a,
      prog_ok
        (fun d state =>
           {|
             pre :=
               (* for simplicity we only consider in-bounds addresses, though if
                  a is out-of-bounds fixup just might uselessly write to disk and not do
                  anything *)
               a < size d /\
               TD.disk0 state |= eq d /\
               TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                match r with
                | Continue =>
                  TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d
                | RepairDone =>
                  TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d
                | DiskFailed i =>
                  TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d
                end;
             crash :=
               fun state' =>
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
           |})
        (fixup a)
        TD.step.
  Proof.
    unfold fixup.
    step.
    descend; intuition eauto.

    destruct r; step.
    descend; intuition eauto.

    destruct r; try step.
    is_eq v v0; try step.
    assert (v = v0) by eauto using disks_eq_inbounds.
    contradiction.
  Qed.

  Lemma diskUpd_maybe_same : forall (d:disk) a b,
      d a |= eq b ->
      diskUpd d a b = d.
  Proof.
    intros.
    destruct (d a) eqn:?; simpl in *; subst;
      autorewrite with upd;
      auto.
  Qed.

  Hint Rewrite diskUpd_maybe_same using (solve [ auto ]) : upd.

  Theorem fixup_correct_addr_ok : forall a,
      prog_ok
        (fun '(d, b) state =>
           {|
             pre :=
               a < size d /\
               TD.disk0 state |= eq (diskUpd d a b) /\
               TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                match r with
                | Continue =>
                  (* could happen if b already happened to be value *)
                  TD.disk0 state' |= eq (diskUpd d a b) /\
                  TD.disk1 state' |= eq (diskUpd d a b)
                | RepairDone =>
                  TD.disk0 state' |= eq (diskUpd d a b) /\
                  TD.disk1 state' |= eq (diskUpd d a b)
                | DiskFailed i =>
                  match i with
                  | d0 => TD.disk0 state' |= eq d /\
                         TD.disk1 state' |= eq d
                  | d1 => TD.disk0 state' |= eq (diskUpd d a b) /\
                         TD.disk1 state' |= eq (diskUpd d a b)
                  end
                end;
             crash :=
               fun state' =>
               (TD.disk0 state' |= eq (diskUpd d a b) /\
                TD.disk1 state' |= eq d) \/
               (TD.disk0 state' |= eq d /\
                TD.disk1 state' |= eq d);
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
    is_eq b v; try step.
    descend; intuition eauto.

    step.
    destruct r; intuition eauto; simplify; finish.
  Qed.

  Theorem fixup_wrong_addr_ok : forall a,
      prog_ok
        (fun '(d, b, a') state =>
           {|
             pre :=
               a < size d /\
               (* recovery, working from end of disk, has not yet reached the
                  correct address *)
               a' < a /\
               TD.disk0 state |= eq (diskUpd d a' b) /\
               TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                match r with
                | Continue =>
                  TD.disk0 state' |= eq (diskUpd d a' b) /\
                  TD.disk1 state' |= eq d
                | RepairDone =>
                  (* since the address is wrong, the only way we finish is if a
                  disk fails, which we explicitly report *)
                  False
                | DiskFailed i =>
                  match i with
                  | d0 => TD.disk0 state' |= eq d /\
                         TD.disk1 state' |= eq d
                  | d1 => TD.disk0 state' |= eq (diskUpd d a' b) /\
                         TD.disk1 state' |= eq (diskUpd d a' b)
                  end
                end;
             crash :=
               fun state' =>
               (TD.disk0 state' |= eq (diskUpd d a' b) /\
                TD.disk1 state' |= eq d) \/
               (TD.disk0 state' |= eq d /\
                TD.disk1 state' |= eq d);
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
    is_eq v v0; try step.
    descend; intuition eauto.

    step.
    destruct r; intuition eauto; simplify; finish.
    assert (a' <> a) by eauto using PeanoNat.Nat.lt_neq.
    autorewrite with upd in *.
    assert (v = v0) by eauto using disks_eq_inbounds.
    contradiction.
  Qed.

  Theorem fixup_ok : forall a,
      prog_ok
        (fun '(d, b, a') state =>
           {|
             pre :=
               a < size d /\
               ((a' <= a /\
                 TD.disk0 state |= eq (diskUpd d a' b) /\
                 TD.disk1 state |= eq d) \/
                (TD.disk0 state |= eq d /\
                 TD.disk1 state |= eq d));
             post :=
               fun r state' =>
                 match r with
                 | Continue =>
                   (a' < a /\
                    TD.disk0 state' |= eq (diskUpd d a' b) /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq (diskUpd d a' b) /\
                    TD.disk1 state' |= eq (diskUpd d a' b))
                 | RepairDone =>
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d) \/
                   (a = a' /\ (* not necessary, but nice to document *)
                    TD.disk0 state' |= eq (diskUpd d a' b) /\
                    TD.disk1 state' |= eq (diskUpd d a' b))
                 | DiskFailed i =>
                   match i with
                   | d0 => TD.disk0 state' |= eq d /\
                          TD.disk1 state' |= eq d
                   | d1 => (TD.disk0 state' |= eq (diskUpd d a' b) /\
                           TD.disk1 state' |= eq (diskUpd d a' b)) \/
                          (* needed for precondition where both disks are just
                          d *)
                          (TD.disk0 state' |= eq d /\
                           TD.disk0 state' |= eq d)
                   end
                 end;
             crash :=
               fun state' =>
                 (TD.disk0 state' |= eq (diskUpd d a' b) /\
                  TD.disk1 state' |= eq d) \/
                 (TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d);
           |})
        (fixup a)
        TD.step.
  Proof.
    intro_begin; simplify.
    intuition eauto.
    apply PeanoNat.Nat.lt_eq_cases in H2; intuition.
    - step_prog_with ltac:(eapply fixup_wrong_addr_ok); simplify; finish.
      descend; intuition eauto.

      step.
      destruct r; intuition eauto.
      destruct i; intuition eauto.
    - step_prog_with ltac:(eapply fixup_correct_addr_ok); simplify; finish.
      descend; intuition eauto.

      step.
      destruct r; intuition eauto.
      destruct i; intuition eauto.
    - step_prog_with ltac:(eapply fixup_equal_ok); simplify; finish.
      descend; intuition eauto.

      step.
      destruct r; intuition eauto.
      destruct i; intuition eauto.
  Qed.

  Hint Extern 1 {{ fixup _; _ }} => apply fixup_ok : prog.

  Hint Resolve Lt.lt_n_Sm_le.

  Theorem recover_at_ok : forall a,
      prog_ok
        (fun '(d, b, a') state =>
           {|
             pre :=
               a <= size d /\
               ((a' < a /\
                 TD.disk0 state |= eq (diskUpd d a' b) /\
                 TD.disk1 state |= eq d) \/
                (TD.disk0 state |= eq d /\
                 TD.disk1 state |= eq d));
             post :=
               fun r state' =>
                 match r with
                 | Continue => False
                 | RepairDone =>
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq (diskUpd d a' b) /\
                    TD.disk1 state' |= eq (diskUpd d a' b))
                 | DiskFailed i =>
                   match i with
                   | d0 => TD.disk0 state' |= eq d /\
                          TD.disk1 state' |= eq d
                   | d1 => (TD.disk0 state' |= eq (diskUpd d a' b) /\
                           TD.disk1 state' |= eq (diskUpd d a' b)) \/
                          (* needed for precondition where both disks are just
                          d *)
                          (TD.disk0 state' |= eq d /\
                           TD.disk0 state' |= eq d)
                   end
                 end;
             crash :=
               fun state' =>
                 (TD.disk0 state' |= eq (diskUpd d a' b) /\
                  TD.disk1 state' |= eq d) \/
                 (TD.disk0 state' |= eq d /\
                  TD.disk1 state' |= eq d);
           |})
        (recover_at a)
        TD.step.
  Proof.
    induction a; simpl; intros.
    - eapply ret_prog_ok; simplify; finish.
      intuition eauto.
      inversion H0.
    - step.
      descend; intuition eauto.

      destruct r; step.
      intuition (eauto);
        try solve [ descend; intuition eauto ].
      exists (diskUpd d a' b), block0, 0; intuition eauto.
      autorewrite with upd; eauto.

      destruct r; step.
      intuition eauto.
      (* actually, need some correlation between precondition cases and
      postcondition cases for fixup *)
  Abort.

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

  (* TODO: get this in recovery through the programming language *)
  Axiom disk_size : nat.

  Theorem RD_ok : interpretation
                    op_impl
                    (Recover disk_size)
                    TD.step D.step
                    invariant
                    abstraction.
  Proof.
    eapply interpret_exec; intros; eauto.
    - destruct op; simpl in *.
      + admit. (* need a recovery spec for Read *)
      + admit. (* need a recovery spec for Write *)
    - (* prove recovery correctly works when not doing anything (the invariant
         is already true) *)
      eapply idempotent_loopspec.
      all: admit.
  Abort.

End RD.
