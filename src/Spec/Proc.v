Section Proc.

  Variable Op:Type.

  Inductive proc :=
  | Ret
  | Call (op:Op) (p:proc)
  | Spawn (p:proc)
  | Atomic (p:proc)
  .

End Proc.
