Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailServerLockAbsAPI.
Require Import MailServerLockAbsImpl.
Require Import MailboxAPI.
Require Import MailboxImpl.


Module StringIdx <: HIndex.
  Definition indexT := string.
  Definition indexValid (u : string) := u = "Alice"%string \/ u = "Bob"%string.
  Definition indexCmp := string_Ordering.
End StringIdx.

Module MailServerHOp := HOps MailServerOp StringIdx.
Module MailServerHState := HState MailServerState StringIdx.
Module MailServerHAPI := HLayer MailServerOp MailServerState MailServerAPI StringIdx.

Module MailServerLockAbsHState := HState MailServerLockAbsState StringIdx.
Module MailServerLockAbsHAPI := HLayer MailServerOp MailServerLockAbsState MailServerLockAbsAPI StringIdx.


Module MailServerLockAbsImplH' :=
  LayerImplAbsHT
    MailServerOp
    MailServerLockAbsState MailServerLockAbsAPI
    MailServerState MailServerAPI
    MailServerLockAbsImpl'
    StringIdx.

Module MailServerLockAbsImplH :=
  LayerImplAbs MailServerHOp
    MailServerLockAbsHState MailServerLockAbsHAPI
    MailServerHState        MailServerHAPI
    MailServerLockAbsImplH'.
