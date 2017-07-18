Require Import Disk.SimpleDisk.
Require Import Bytes.

Parameter Handle:Type.

Inductive Request :=
| Read (h:Handle) (off:nat) (blocks:nat)
| Write (h:Handle) (off:nat) (len:nat) (dat:bytes (len*blockbytes))
| Flush (h:Handle)
| Disconnect
| UnknownOp (h:Handle).

Inductive ErrorCode :=
| ESuccess
| EInvalid
| ENospc.

Record Response :=
  { rhandle: Handle;
    error: ErrorCode;
    data_len: nat;
    data: bytes data_len; }.
