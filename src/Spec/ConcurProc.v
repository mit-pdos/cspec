Set Implicit Arguments.

Section Proc.
  Variable Op : Type -> Type.

  Inductive proc : Type -> Type :=
  | Prim : forall T (op : Op T), proc T
  | Ret : forall T (v : T), proc T
  | Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T
  | Until : forall T (c : T -> bool) (p : option T -> proc T) (v : option T), proc T
  | Atomic : forall T (p : proc T), proc T
  | Spawn : forall T (p: proc T), proc unit
  .

  Inductive maybe_proc :=
  | Proc : forall T, proc T -> maybe_proc
  | NoProc.
End Proc.

Arguments Prim {Op T}.
Arguments Ret {Op T}.
Arguments Bind {Op T T1}.
Arguments Until {Op T}.
Arguments Atomic {Op T}.

Arguments Proc {Op T}.
Arguments NoProc {Op}.
