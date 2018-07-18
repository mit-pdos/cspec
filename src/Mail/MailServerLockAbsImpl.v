Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailServerLockAbsAPI.

Module MailServerLockAbsImpl' <:
  LayerImplAbsT MailServerOp
    MailServerLockAbsState MailServerLockAbsAPI
    MailServerState MailServerAPI.

  Import MailServerLockAbsState.

  Definition absR (s1 : MailServerLockAbsState.State) (s2 : MailServerState.State) :=
    MailServerLockAbsState.maildir s1 = s2.

  Hint Extern 1 (MailServerAPI.step _ _ _ _ _ _) => econstructor.

  Theorem absR_ok :
    op_abs absR MailServerLockAbsAPI.step MailServerAPI.step.
  Proof.
    unfold op_abs; intros.
    unfold absR in *.
    inversion H0; clear H0; subst; repeat sigT_eq.
    all: eauto.
  Qed.

  Theorem absInitP :
    forall s1 s2,
      MailServerLockAbsState.initP s1 ->
      absR s1 s2 ->
      MailServerAPI.MailServerState.initP s2.
  Proof.
    eauto.
  Qed.

End MailServerLockAbsImpl'.

Module MailServerLockAbsImpl :=
  LayerImplAbs MailServerOp
    MailServerLockAbsState MailServerLockAbsAPI
    MailServerState MailServerAPI
    MailServerLockAbsImpl'.

Module MailServerLockAbsImplH' :=
  LayerImplAbsHT
    MailServerOp
    MailServerLockAbsState MailServerLockAbsAPI
    MailServerState MailServerAPI
    MailServerLockAbsImpl'
    UserIdx.

Module MailServerLockAbsImplH :=
  LayerImplAbs MailServerHOp
    MailServerLockAbsHState MailServerLockAbsHAPI
    MailServerHState        MailServerHAPI
    MailServerLockAbsImplH'.
