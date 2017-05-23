Require Import Disk.
Require Import Bytes.

Parameter Handle:Type.

Inductive Request :=
| Read (h:Handle) (off:addr) (blocks:nat)
| Write (h:Handle) (off:addr) (len:nat) (dat:bytes (len*blockbytes))
| Disconnect
| UnknownOp (h:Handle).

Inductive ErrorCode :=
| ESuccess
| EInvalid.

Record Response :=
  { rhandle: Handle;
    error: ErrorCode;
    data_len: nat;
    data: bytes data_len; }.
