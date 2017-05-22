Require Import TwoDisk.TwoDiskAPI.
Require Import MaybeHolds.

Lemma both_disks_not_missing : forall state,
    TD.disk0 state |= missing ->
    TD.disk1 state |= missing ->
    False.
Proof.
  destruct state; simpl; intros.
  destruct disk0, disk1; simpl in *; eauto.
Qed.
