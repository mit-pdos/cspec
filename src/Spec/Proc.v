Global Set Implicit Arguments.

Section Proc.

  Context {Op:Type}.

  Inductive proc :=
  | Ret
  | Exec (a:Action) (p:proc)
  with Action :=
       | Call (op:Op)
       | Spawn (p:proc)
       | Atomic (p:proc)
  .

End Proc.

Arguments proc Op : clear implicits.
