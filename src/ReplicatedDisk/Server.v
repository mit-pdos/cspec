Require Import POCS.

Require Import ReplicatedDisk.ReplicatedDiskImpl.
Require Import ReplicatedDisk.ReplicatedDiskAPI.
Require Import TwoDisk.ExtrTwoDisk.

Require Import NBD.NbdData.
Require Import NBD.ExtrServer.

(* TODO: re-use this code for asynchronous implementation *)
Definition d := RD.rd TD.td.

Fixpoint read (off:nat) n : prog (bytes (n*blockbytes)) :=
  match n with
  | 0 => Ret bnull
  | S n => b <- Prim d (RD.Read off);
            rest <- read (off+1) n;
            Ret (bappend b rest)
  end.

Fixpoint write (off:nat) n (bs:bytes (n*blockbytes)) {struct n} : prog unit.
  destruct n.
  - apply (Ret tt).
  - replace (S n * blockbytes) with (blockbytes + n * blockbytes) in * by reflexivity.
    destruct (bsplit bs) as [b rest].
    apply (Bind (Prim d (RD.Write off b))); intros _.
    apply (write (off+1) _ rest).
Defined.

CoFixpoint handle : prog unit :=
  req <- getRequest;
  match req with
  | Read h off blocks =>
    (* TODO: bounds checks *)
    data <- read off blocks;
    _ <- sendResponse
      {| rhandle := h;
         error := ESuccess;
         data := data; |};
    handle
  | Write h off _ dat =>
    _ <- write off _ dat;
    _ <- sendResponse
      {| rhandle := h;
         error := ESuccess;
         data := bnull |};
    handle
  | Flush h =>
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

Definition diskSize : prog nat :=
  Prim d RD.DiskSize.

Definition serverLoop : prog unit :=
  _ <- irec d;
  handle.

Definition init := iInit d.
