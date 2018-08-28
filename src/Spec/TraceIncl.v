Require Import Spec.Proc.
Require Import Spec.Exec.

Section Semantics.
  Variable Op:Type.
  Variable State:Type.
  Variable step: InstStep Op State.

  Notation exec := (exec step).

  Implicit Types (op:Op) (p: proc Op) (s:State) (tr:trace).

  Definition trace_incl p1 p2 :=
    forall ts tid,
    forall s s' tr tr' ts1',
      exec (ts [[tid := p1]], s, tr) (ts1', s', tr') ->
      exists ts2', exec (ts [[tid := p2]], s, tr) (ts2', s', tr').

End Semantics.
