Require Import Disk.

(* mirrors the structure of the two disk modularity, even though everything is
much shorter here *)

Module D.

  Inductive Op : Type -> Type :=
  | Read (a:addr) : Op block
  | Write (a:addr) (b:block) : Op unit
  | Sync : Op unit
  | DiskSize : Op nat.

End D.
