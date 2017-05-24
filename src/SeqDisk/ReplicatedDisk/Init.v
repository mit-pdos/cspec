Require Import Omega.

Require Import Automation.
Require Import Disk.

Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import TwoDisk.TwoDiskAPI.
Require Import TwoDisk.TwoDiskTheorems.
Require Import
        SeqDisk.ReplicatedDisk.Step
        SeqDisk.ReplicatedDisk.TwoDiskFacts.

Require Import MaybeHolds.

Section Init.

  Variable (td:Interface TD.API).

  Fixpoint init_at (a:nat) : prog unit :=
    match a with
    | 0 => Ret tt
    | S a => _ <- Prim td (TD.Write d0 a block0);
              _ <- Prim td (TD.Write d1 a block0);
              init_at a
    end.

  Definition DiskSizes : prog (nat * nat + nat) :=
    sz1 <- Prim td (TD.DiskSize d0);
      match sz1 with
      | Working sz1 => sz2 <- Prim td (TD.DiskSize d1);
                        match sz2 with
                        | Working sz2 => if sz1 == sz2 then
                                          Ret (inr sz1)
                                        else Ret (inl (sz1, sz2))
                        | Failed => Ret (inr sz1)
                        end
      | Failed => sz2 <- Prim td (TD.DiskSize d1);
                   match sz2 with
                   | Working sz2 => Ret (inr sz2)
                   | Failed => Ret (inl (0, 0)) (* impossible *)
                   end
      end.

  Definition Init : prog InitResult :=
    sizes <- DiskSizes;
      match sizes with
      | inr sz => _ <- init_at sz;
                   Ret Initialized
      | inl _ => Ret InitFailed
      end.

  Lemma le_eq_or_S_le : forall n m,
      n <= m ->
      n = m \/
      S n <= m /\ n <> m.
  Proof.
    intros.
    omega.
  Qed.

  Definition equal_after a (d_0 d_1: disk) :=
    size d_0 = size d_1 /\
    forall a', a <= a' -> d_0 a' = d_1 a'.

  Lemma equal_after_diskUpd : forall a d_0 d_1 b,
      equal_after (S a) d_0 d_1 ->
      equal_after a (diskUpd d_0 a b) (diskUpd d_1 a b).
  Proof.
    unfold equal_after; intuition.
    autorewrite with upd; eauto.
    apply le_eq_or_S_le in H; intuition subst.
    destruct (lt_dec a' (size d_0)); autorewrite with upd.
    assert (a' < size d_1) by congruence; autorewrite with upd; auto.
    assert (~a' < size d_1) by congruence; autorewrite with upd; auto.
    autorewrite with upd; eauto.
  Qed.

  Hint Resolve equal_after_diskUpd.

  Theorem init_at_ok : forall a,
      prog_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                TD.disk0 state |= eq d_0 /\
                TD.disk1 state |= eq d_1 /\
                equal_after a d_0 d_1;
              post :=
                fun _ state' =>
                  exists d_0' d_1',
                    TD.disk0 state' |= eq d_0' /\
                    TD.disk1 state' |= eq d_1' /\
                    equal_after 0 d_0' d_1';
              recover :=
                fun _ state' => True;
           |})
        (init_at a)
        (irec td)
        (refinement td).
  Proof.
    induction a; simpl; intros.
    - step.
    - step.

      step.
      destruct r; finish.
      + step.
        destruct r; finish.
      + step.
        destruct r; finish.

        Grab Existential Variables.
        exact block0.
  Qed.

  Hint Resolve init_at_ok.

  Hint Resolve both_disks_not_missing : false.

  Theorem DiskSizes_ok :
      prog_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                TD.disk0 state |= eq d_0 /\
                TD.disk1 state |= eq d_1;
              post :=
                fun r state' =>
                  exists d_0' d_1',
                    TD.disk0 state' |= eq d_0' /\
                    TD.disk1 state' |= eq d_1' /\
                    match r with
                  | inr sz => size d_0' = sz /\
                             size d_1' = sz
                  | inl _ => size d_0 <> size d_1
                  end;
              recover :=
                fun _ state' => True;
           |})
        (DiskSizes)
        (irec td)
        (refinement td).
  Proof.
    unfold DiskSizes; step.
    destruct r; step.
    destruct r; try step.
    is_eq (size d_0) v; step.
    destruct r; step.
  Qed.

  Lemma equal_after_0_to_eq : forall d_0 d_1,
      equal_after 0 d_0 d_1 ->
      d_0 = d_1.
  Proof.
    unfold equal_after; intuition.
    eapply diskMem_ext_eq.
    extensionality a'.
    eapply H1; omega.
  Qed.

  Lemma equal_after_size : forall d_0 d_1,
      size d_0 = size d_1 ->
      equal_after (size d_0) d_0 d_1.
  Proof.
    unfold equal_after; intuition.
    assert (~a' < size d_0) by omega.
    assert (~a' < size d_1) by congruence.
    autorewrite with upd; eauto.
  Qed.

  Hint Resolve equal_after_size.
  Hint Resolve equal_after_0_to_eq.

  Hint Resolve DiskSizes_ok.

  Theorem Init_ok :
      prog_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                TD.disk0 state |= eq d_0 /\
                TD.disk1 state |= eq d_1;
              post :=
                fun r state' =>
                  match r with
                  | Initialized =>
                    exists d_0' d_1',
                    TD.disk0 state' |= eq d_0' /\
                    TD.disk1 state' |= eq d_1' /\
                    d_0' = d_1'
                  | InitFailed => (size d_0 <> size d_1)%type
                  end;
              recover :=
                fun _ state' => True;
           |})
        (Init)
        (irec td)
        (refinement td).
  Proof.
    unfold Init; step.
    step.
    step.
    step.
  Qed.

End Init.

Hint Resolve Init_ok.
