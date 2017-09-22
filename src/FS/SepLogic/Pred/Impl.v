Require Import POCS.

Require Import FS.SepLogic.Pred.Def.

Theorem lift1_left : forall (P: Prop) `(q: pred A V),
    (P -> [| True |] ===> q) ->
    [| P |] ===> q.
Proof.
  unfold pimpl; simpl; intuition.
Qed.
