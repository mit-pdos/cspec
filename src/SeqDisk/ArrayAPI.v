Require Import Bytes.
Require Import Disk.

Require Import SeqDisk.SeqDiskAPI.
Require Import Refinement.ProgLang.
Require Import Refinement.Interface.

Opaque blockbytes.

Section ArrayDisk.

  Variable (d:Interface D.API).

  Fixpoint read (off:nat) n : prog (bytes (n*blockbytes)) :=
    match n with
    | 0 => Ret bnull
    | S n => b <- Prim d (D.Read off);
              rest <- read (off+1) n;
              Ret (bappend b rest)
    end.

  Fixpoint write (off:nat) n (bs:bytes (n*blockbytes)) {struct n} : prog unit.
    destruct n; simpl in *.
    - apply (Ret tt).
    - destruct (bsplit bs) as [b rest].
      apply (Bind (Prim d (D.Write off b))); intros _.
      apply (write (off+1) _ rest).
  Defined.

  Definition recover : prog unit :=
    irec d.

  Definition init : prog InitResult :=
    iInit d.

End ArrayDisk.
