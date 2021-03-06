Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxAPI.
Require Import MailboxTmpAbsAPI.
Require Import MailServerLockAbsAPI.


Module MailboxTmpAbs' <:
  HLayerImplAbsT MailboxOp
    MailboxTmpAbsState MailboxTmpAbsAPI
    MailServerLockAbsState MailboxAPI.

  Import MailboxTmpAbsState.

  Definition absR (s1 : MailboxTmpAbsState.State) (s2 : MailServerLockAbsState.State) :=
    MailboxTmpAbsState.maildir s1 = MailServerLockAbsState.maildir s2 /\
    (MailboxTmpAbsState.locked s1 = false <-> MailServerLockAbsState.locked s2 = None).

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.

  Theorem absR_ok :
    op_abs absR MailboxTmpAbsAPI.step MailboxAPI.step.
  Proof.
    unfold op_abs, absR; intros.
    destruct s1.
    destruct s2.
    intuition idtac.
    simpl in *; subst.
    inversion H0; clear H0; subst; repeat sigT_eq.
    all: simpl.
    all: eexists; split; [ | eauto ].
    all: simpl.
    all: try intuition congruence.
    all: try ( destruct locked1; try intuition congruence ).
    all: eauto.
    simpl.
    intuition congruence.
  Qed.

  Hint Resolve absR_ok.

  Definition initP_map (s1: MailboxTmpAbsState.State) :
    {s2:MailServerLockAbsState.State |
     initP s1 -> absR s1 s2 /\
                MailServerLockAbsState.initP s2}.
    unfold initP, absR, MailServerLockAbsState.initP.
    exists_econstructor; intuition eauto.
  Defined.

End MailboxTmpAbs'.

Module MailboxTmpAbsImpl :=
  HLayerImplAbs MailboxOp
   MailboxTmpAbsState MailboxTmpAbsAPI
   MailServerLockAbsState MailboxAPI
   MailboxTmpAbs'.

Module MailboxTmpAbsH' :=
  LayerImplAbsHT
    MailboxOp
    MailboxTmpAbsState MailboxTmpAbsAPI
    MailServerLockAbsState MailboxAPI
    MailboxTmpAbs'
    UserIdx.

Module MailboxTmpAbsImplH :=
  LayerImplAbs MailboxHOp
    MailboxTmpAbsHState     MailboxTmpAbsHAPI
    MailServerLockAbsHState MailboxHAPI
    MailboxTmpAbsH'.
