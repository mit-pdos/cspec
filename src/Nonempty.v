Require Import Lists.List.

Set Implicit Arguments.

Inductive nonempty T :=
| necons (x:T) (xs:list T).

Definition head T (l:nonempty T) : T :=
  let (x, _) := l in x.

Definition tail T (l:nonempty T) : list T :=
  let (_, xs) := l in xs.

Definition last T (l:nonempty T) : T :=
  let (x, xs) := l in List.last xs x.

Definition prepend T (a:T) (l:nonempty T) : nonempty T :=
  let (x, xs) := l in
  necons a (x::xs).

Definition keep1 T (l:nonempty T) : nonempty T :=
  let (x, _) := l in necons x nil.
