Require Import CSPEC.
Require Import MailServerAPI.
Require Import MailboxAPI.
Require Import MailboxTmpAbsAPI.
Require Import MailServerLockAbsAPI.


Module MailboxTmpAbs'.
  Import Layer.
  Import MailboxTmpAbsState.

  Definition absR (s1 : MailboxTmpAbsState.State) (s2 : MailServerLockAbsState.State) :=
    MailboxTmpAbsState.maildir s1 = MailServerLockAbsState.maildir s2 /\
    (MailboxTmpAbsState.locked s1 = false <-> MailServerLockAbsState.locked s2 = None).

  Hint Extern 1 (MailboxAPI.step _ _ _ _ _ _) => econstructor.

  Theorem absR_ok :
    op_abs absR MailboxTmpAbsAPI.l.(step) MailboxAPI.l.(step).
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

  (* Sydney: I'm fairly sure this should be an HLayerImpl.t and not an
  HLayerImplAbsT.t? *)
  Print HLayerImpl.t.
  Definition l : HLayerImpl.t MailboxTmpAbsAPI.l MailboxAPI.l.
    exact {| HLayerImpl.absR := absR;
             HLayerImpl.absR_ok := absR_ok;
             HLayerImpl.initP_map := initP_map; |}.
  Defined.

End MailboxTmpAbs'.

Definition MailboxTmpAbsImpl := HLayerImplAbs.t MailboxTmpAbs'.l.

Definition MailboxTmpAbsH' := LayerImplAbsHT.t MailboxTmpAbs'.l UserIdx.idx.

Definition MailboxTmpAbsImplH := LayerImplAbs.t MailboxTmpAbsH'.
