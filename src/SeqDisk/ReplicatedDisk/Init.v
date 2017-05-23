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

  Definition Init : prog InitResult :=
    sz1 <- Prim td (TD.DiskSize d0);
      match sz1 with
      | Working sz1 => sz2 <- Prim td (TD.DiskSize d1);
                        match sz2 with
                        | Working sz2 => if sz1 == sz2 then
                                          _ <- init_at sz1;
                                            Ret Initialized
                                        else Ret InitFailed
                        | Failed => _ <- init_at sz1;
                                     Ret Initialized
                        end
      | Failed => sz2 <- Prim td (TD.DiskSize d1);
                   match sz2 with
                   | Working sz2 => _ <- init_at sz2;
                                     Ret Initialized
                   | Failed => Ret InitFailed (* impossible *)
                   end
      end.

  Lemma le_eq_or_S_le : forall n m,
      n <= m ->
      n = m \/
      S n <= m /\ n <> m.
  Proof.
    inversion 1; eauto.
    right; intuition eauto using le_n_S.
    subst.
    eapply PeanoNat.Nat.nle_succ_diag_l; eauto.
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
      descend; intuition eauto.

      step.
      destruct r.
      + descend; intuition eauto.
        step.
        destruct r.
        descend; intuition eauto.

        simplify.
        descend; intuition eauto.
      + descend; intuition eauto.
        step.
        destruct r; simplify.
        descend; intuition eauto; simplify.
        descend; (intuition eauto); simplify.

        Grab Existential Variables.
        exact block0.
  Qed.

  Lemma equal_after_0_to_eq : forall d_0 d_1,
      equal_after 0 d_0 d_1 ->
      d_0 = d_1.
  Proof.
    unfold equal_after; intuition.
    eapply diskMem_ext_eq.
    extensionality a'.
    eauto using le_0_n.
  Qed.

End Init.
