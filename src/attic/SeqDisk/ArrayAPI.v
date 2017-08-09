Require Import Bytes.
Require Import Disk.SimpleDisk.

Require Import SeqDisk.SeqDiskAPI.
Require Import Refinement.ProgLang.
Require Import Refinement.Interface.

Opaque blockbytes.

(* TODO: re-use this code for asynchronous single-disk API *)

Section ArrayDisk.

  Variable (d:Interface D.API).

  Fixpoint read (off:nat) n : proc (bytes (n*blockbytes)) :=
    match n with
    | 0 => Ret bnull
    | S n => b <- Prim d (D.Read off);
              rest <- read (off+1) n;
              Ret (bappend b rest)
    end.

  Fixpoint write (off:nat) n (bs:bytes (n*blockbytes)) {struct n} : proc unit.
    destruct n; simpl in *.
    - apply (Ret tt).
    - destruct (bsplit bs) as [b rest].
      apply (Bind (Prim d (D.Write off b))); intros _.
      apply (write (off+1) _ rest).
  Defined.

  Definition sync : proc unit :=
    Prim d (D.Sync).

  Definition recover: proc unit :=
    irec d.

  Definition init : proc InitResult :=
    iInit d.

End ArrayDisk.
