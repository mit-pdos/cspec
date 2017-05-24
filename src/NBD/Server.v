Require Import Bytes.

Require Import Refinement.ProgLang.Prog.
Require Import SeqDisk.ArrayAPI.
Require Import SeqDisk.ReplicatedDisk.
Require Import SeqDisk.ReplicatedDisk.Init.
Require Import TwoDisk.TwoDiskImpl.

Require Import NBD.NbdData.

Axiom getRequest : prog Request.
Axiom sendResponse : Response -> prog unit.

Definition d := RD.rd TD.td.

CoFixpoint handle : prog unit :=
  req <- getRequest;
    match req with
    | Read h off blocks =>
      (* TODO: bounds checks *)
      data <- read d off blocks;
        _ <- sendResponse
          {| rhandle := h;
             error := ESuccess;
             data := data; |};
        handle
    | Write h off _ dat =>
      _ <- write d off _ dat;
        _ <- sendResponse
          {| rhandle := h;
             error := ESuccess;
             data := bnull |};
        handle
    | UnknownOp h =>
      _ <- sendResponse
        {| rhandle := h;
           error := EInvalid;
           data := bnull |};
        handle
    | Disconnect => Ret tt
    end.

Definition diskSizes : prog (nat * nat + nat) :=
  DiskSizes TD.td.

Definition serverLoop : prog unit :=
  _ <- ArrayAPI.recover d;
    handle.

Definition init := ArrayAPI.init d.
