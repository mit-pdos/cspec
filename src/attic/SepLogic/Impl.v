Require Import MemState.Pred.Def.

Theorem lift1_left : forall (P: Prop) `(q: pred A V),
    (P -> [| True |] ===> q) ->
    [| P |] ===> q.
Proof.
  unfold pimpl; simpl; intuition.
Qed.
