Require Import POCS.

Require Import ReplicatedDisk.ReplicatedDiskImpl.
Require Import TwoDisk.TwoDiskImpl.
Require Import TwoDisk.TwoDiskBaseImpl.

Require Import NBD.NbdData.
Require Import NBD.ExtrServer.


Module td := TwoDisk TwoDiskBase.
Module rd := ReplicatedDisk td.

Fixpoint read (off:nat) n : prog (bytes (n*blockbytes)) :=
  match n with
  | 0 => Ret bnull
  | S n => b <- rd.read off;
            rest <- read (off+1) n;
            Ret (bappend b rest)
  end.

Fixpoint write (off:nat) n (bs:bytes (n*blockbytes)) {struct n} : prog unit.
  destruct n.
  - apply (Ret tt).
  - replace (S n * blockbytes) with (blockbytes + n * blockbytes) in * by reflexivity.
    destruct (bsplit bs) as [b rest].
    apply (Bind (rd.write off b)); intros _.
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
  rd.diskSize.

Definition serverLoop : prog unit :=
  _ <- rd.recover;
  handle.

Definition init := rd.init.
