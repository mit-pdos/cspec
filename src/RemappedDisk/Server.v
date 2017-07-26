Require Import POCS.

Require Import RemappedDisk.RemappedDiskAPI.
Require Import RemappedDisk.RemappedDiskImpl.
Require Import BadSectorDisk.ExtrBadSectorDisk.

Require Import NBD.NbdData.
Require Import NBD.ExtrServer.

(* TODO: re-use this code for asynchronous implementation *)
Definition d := RemappedDisk.rd BadSectorDisk.bs.

Opaque blockbytes.

Fixpoint read (off:nat) n : prog (bytes (n*blockbytes)) :=
  match n with
  | 0 => Ret bnull
  | S n => b <- Prim d (RemappedDisk.Read off);
            rest <- read (off+1) n;
            Ret (bappend b rest)
  end.

Fixpoint write (off:nat) n (bs:bytes (n*blockbytes)) {struct n} : prog unit.
  destruct n; simpl in *.
  - apply (Ret tt).
  - destruct (bsplit bs) as [b rest].
    apply (Bind (Prim d (RemappedDisk.Write off b))); intros _.
    apply (write (off+1) _ rest).
Defined.

CoFixpoint handle : prog unit :=
  req <- getRequest;
  match req with
  | Read h off blocks =>
    (* TODO: bounds checks *)
    data <- read off blocks;
    _ <- sendResponse
      {| rhandle := h; error := ESuccess; data := data; |};
    handle
  | Write h off _ dat =>
    _ <- write off _ dat;
    _ <- sendResponse
      {| rhandle := h; error := ESuccess; data := bnull |};
    handle
  | Flush h =>
    _ <- sendResponse
      {| rhandle := h; error := ESuccess; data := bnull |};
    handle
  | UnknownOp h =>
    _ <- sendResponse
      {| rhandle := h; error := EInvalid; data := bnull |};
    handle
  | Disconnect => Ret tt
  end.

Definition serverLoop : prog unit :=
  _ <- irec d;
  handle.

Definition diskSize : prog nat :=
  Prim d (RemappedDisk.DiskSize).

Definition init := iInit d.
