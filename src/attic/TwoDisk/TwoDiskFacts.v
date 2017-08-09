Require Import TwoDisk.TwoDiskDefs.
Require Import MaybeHolds.

Theorem both_disks_not_missing : forall diskT (state: TD.State diskT),
    TD.disk0 state |= missing ->
    TD.disk1 state |= missing ->
    False.
Proof.
  destruct state; simpl; intros.
  destruct disk0, disk1; simpl in *; eauto.
Qed.
