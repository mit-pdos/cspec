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


Module AtomicReaderH' :=
  LayerImplMoversProtocolHT
    MailServerLockAbsState
    MailboxOp    MailboxAPI MailboxRestrictedAPI
    MailServerOp MailServerLockAbsAPI
    MailboxProtocol
    AtomicReader'
    StringIdx.

Module MailboxHOp := HOps MailboxOp StringIdx.
Module MailboxHAPI := HLayer MailboxOp MailServerLockAbsState MailboxAPI StringIdx.
Module MailboxRestrictedHAPI := HLayer MailboxOp MailServerLockAbsState MailboxRestrictedAPI StringIdx.
Module MailboxHProtocol := HProtocol MailboxOp MailServerLockAbsState MailboxProtocol StringIdx.

Module AtomicReaderH :=
  LayerImplMoversProtocol
    MailServerLockAbsHState
    MailboxHOp    MailboxHAPI MailboxRestrictedHAPI
    MailServerHOp MailServerLockAbsHAPI
    MailboxHProtocol
    AtomicReaderH'.

Module xx :=
  Link
    MailboxHOp    MailServerLockAbsHState MailboxHAPI
    MailServerHOp MailServerLockAbsHState MailServerLockAbsHAPI
    MailServerHOp MailServerHState        MailServerHAPI
    AtomicReaderH MailServerLockAbsImplH.
