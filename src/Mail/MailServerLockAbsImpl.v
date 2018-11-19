Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailServerLockAbsAPI.

Module MailServerLockAbsImpl'.

  Import MailServerLockAbsState.
  Import Layer.

  Definition absR (s1 : MailServerLockAbsState.State) (s2 : MailServerState.State) :=
    MailServerLockAbsState.maildir s1 = s2.

  Hint Extern 1 (MailServerAPI.l.(step) _ _ _ _ _ _) => econstructor.

  Theorem absR_ok :
    op_abs absR MailServerLockAbsAPI.l.(step) MailServerAPI.l.(step).
  Proof.
    unfold op_abs; intros.
    unfold absR in *.
    inversion H0; clear H0; subst; repeat sigT_eq.
    all: eauto.
  Qed.

  Definition initP_map (s1: MailServerLockAbsState.State) :
    {s2: MailServerState.State | MailServerLockAbsState.initP s1 -> absR s1 s2 /\ MailServerState.initP s2}.
    exists (maildir s1).
    unfold initP, absR, MailServerState.initP; eauto.
  Defined.

  Definition l : HLayerImpl.t MailServerLockAbsAPI.l MailServerAPI.l.
    refine {| HLayerImpl.absR := absR;
              HLayerImpl.absR_ok := absR_ok;
              HLayerImpl.initP_map := initP_map; |}.
  Defined.

End MailServerLockAbsImpl'.

Definition MailServerLockAbsImpl := HLayerImplAbs.t MailServerLockAbsImpl'.l.

Definition MailServerLockAbsImplH' := LayerImplAbsHT.t MailServerLockAbsImpl'.l UserIdx.idx.

Definition MailServerLockAbsImplH := LayerImplAbs.t MailServerLockAbsImplH'.
