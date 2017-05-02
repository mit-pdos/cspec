Require Import SepLogic.Mem.Def.
Require Import SepLogic.Pred.Def.

Definition mem_is `(m: mem A V) : pred A V :=
  mkPred (fun m' => m' = m).

Theorem mem_is_extract : forall `(m: mem A V) m',
    m' |= mem_is m ->
    m' = m.
Proof.
  eauto.
Qed.

Theorem mem_is_eq : forall `(m: mem A V) m',
    m' = m ->
    m' |= mem_is m.
Proof.
  eauto.
Qed.

Opaque mem_is.
