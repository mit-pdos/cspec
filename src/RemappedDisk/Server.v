Require Import POCS.

Require Import RemappedDisk.RemappedDiskImpl.
Require Import BadSectorDisk.BadSectorImpl.
Require Import NBD.NbdImpl.
Require Import NBD.NbdAPI.


Module d := RemappedDisk BadSectorDisk.
Module nbd := NbdImpl.

Fixpoint read (off:nat) n : prog (bytes (n*blockbytes)) :=
  match n with
  | 0 => Ret bnull
  | S n => b <- d.read off;
            rest <- read (off+1) n;
            Ret (bappend b rest)
  end.

Fixpoint write (off:nat) n (bs:bytes (n*blockbytes)) {struct n} : prog unit.
  destruct n.
  - apply (Ret tt).
  - destruct (bsplit bs) as [b rest].
    apply (Bind (d.write off b)); intros _.
    apply (write (off+1) _ rest).
Defined.

CoFixpoint handle : prog unit :=
  req <- nbd.getRequest;
  match req with
  | Read h off blocks =>
    (* TODO: bounds checks *)
    data <- read off blocks;
    _ <- nbd.sendResponse
      {| rhandle := h; error := ESuccess; data := data; |};
    handle
  | Write h off _ dat =>
    _ <- write off _ dat;
    _ <- nbd.sendResponse
      {| rhandle := h; error := ESuccess; data := bnull |};
    handle
  | Flush h =>
    _ <- nbd.sendResponse
      {| rhandle := h; error := ESuccess; data := bnull |};
    handle
  | UnknownOp h =>
    _ <- nbd.sendResponse
      {| rhandle := h; error := EInvalid; data := bnull |};
    handle
  | Disconnect => Ret tt
  end.

Definition serverLoop : prog unit :=
  _ <- d.recover;
  handle.

Definition diskSize : prog nat :=
  d.diskSize.

Definition init := d.init.
