Require Import Automation.

Require Import SepLogic.Mem.Def.
Require Import SepLogic.Pred.Def.

Theorem ptsto_valid : forall `(m: mem A V) F a v,
    m |= F * a |-> v ->
    m a = Some v.
Proof.
  intros.
  apply star_comm in H.
  simpl in *; repeat deex.
  unfold mem_union; simpl_match; auto.
Qed.
