Require Import List.
Require Import Ordering.
Require Import ProofIrrelevance.

Set Implicit Arguments.

Module FMap.

  Section Maps.

    Variable A:Type.
    Variable V:Type.
    Context {Acmp: Ordering A}.

    Record t :=
      { elements : list (A * V);
      }.
    Axiom empty : t.

    Axiom MapsTo : A -> V -> t -> Prop.

    Definition keys (m:t) : list A.
    Admitted.

    Definition In (k : A) (m : t) :=
      List.In k (keys m).

    Theorem empty_in : forall x,
        ~In x empty.
    Admitted.

    Theorem empty_mapsto : forall x v,
        ~MapsTo x v empty.
    Admitted.

    Definition In_dec x s : {In x s} + {~In x s}.
    Admitted.

    Definition add (x:A) (v:V) (s:t) : t.
    Admitted.

    Definition remove (x:A) (s:t) : t.
    Admitted.

    Theorem in_add :
      forall a1 a2 v m,
        In a1 m ->
        In a1 (add a2 v m).
    Admitted.

    Theorem in_add_ne :
      forall a1 a2 v m,
        In a1 (add a2 v m) ->
        a1 <> a2 ->
        In a1 m.
    Admitted.

    Theorem in_remove :
      forall a1 a2 m,
        In a1 (remove a2 m) ->
        In a1 m.
    Admitted.

    Theorem in_remove_ne :
      forall a1 a2 m,
        In a1 m ->
        a1 <> a2 ->
        In a1 (remove a2 m).
    Admitted.

    Theorem add_add_ne :
      forall a1 v1 a2 v2 m,
        a1 <> a2 ->
        add a1 v1 (add a2 v2 m) = add a2 v2 (add a1 v1 m).
    Admitted.

    Theorem add_add :
      forall a v1 v2 m,
        add a v1 (add a v2 m) = add a v1 m.
    Admitted.

    Theorem add_remove_ne :
      forall a1 v1 a2 m,
        a1 <> a2 ->
        add a1 v1 (remove a2 m) = remove a2 (add a1 v1 m).
    Admitted.

    Theorem remove_remove :
      forall a1 a2 m,
        remove a1 (remove a2 m) = remove a2 (remove a1 m).
    Admitted.

    Theorem remove_add :
      forall a1 v1 m,
        ~ In a1 m ->
        remove a1 (add a1 v1 m) = m.
    Admitted.

    Theorem mapsto_add_ne :
      forall a1 v1 a2 v2 m,
        MapsTo a1 v1 (add a2 v2 m) ->
        a1 <> a2 ->
        MapsTo a1 v1 m.
    Admitted.

    Theorem mapsto_remove_ne :
      forall a1 v1 a2 m,
        MapsTo a1 v1 m ->
        a1 <> a2 ->
        MapsTo a1 v1 (remove a2 m).
    Admitted.

    Theorem mapsto_add :
      forall a1 v1 v1' m,
        MapsTo a1 v1 (add a1 v1' m) ->
        v1 = v1'.
    Admitted.

  End Maps.

End FMap.
