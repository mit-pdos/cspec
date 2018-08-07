Set Implicit Arguments.

(** Reader is the reader monad (or just the function monad). We only use
Applicative here. *)
Definition Reader E T := forall (e:E), T e.
Arguments Reader : clear implicits.

Definition pure {E T} (x:T) : Reader E (fun _ => T) := fun _ => x.

Definition ap {E}
           {A: E -> Type}
           {B: forall (e:E), A e -> Type}
           (f: Reader E (fun e => forall (a:A e), B e a)) :
  forall (x: Reader E A), Reader E (fun e => B e (x e))  :=
  fun x => fun e => f e (x e).
Infix "<*>" := (ap) (at level 11, left associativity).

(** Settable is a way of accessing a constructor for a record of type T. The
syntactic form of this definition is important: it must be an eta-expanded
version of T's constructor, written generically over the field accessors of T.
The best way to do this for a record X := mkX { A; B; C} is [pure mkX <*> A <*>
B <*> C]. *)
Class Settable T := { mkT: Reader T (fun _ => T);
                      mkT_ok: forall x, mkT x = x }.
Arguments mkT T mk : clear implicits, rename.

Local Ltac mkSettable e :=
  refine {| mkT := e |};
  (match goal with
   | |- forall x, _ = _ => solve [ destruct x; cbv; f_equal ]
   end).

(** mkSettable creates an instance of Settable from an expression like [pure mkX
<*> A <*> B <*> C] *)
Notation mkSettable e := (ltac:(mkSettable e)) (only parsing).

(** [setter] creates a setter based on an eta-expanded record constructor and a
particular field projection proj *)
Local Ltac setter etaT proj :=
  let set :=
      (match eval pattern proj in etaT with
       | ?setter ?proj => constr:(fun x => setter (pure x))
       end) in
  let set := (eval cbv [pure ap] in set) in
  exact set.

(* Combining the above, [getSetter'] looks up the eta-expanded version of T with
the Settable typeclass, and calls [setter] to create a setter. *)
Local Ltac get_setter T proj :=
  match constr:(mkT T _) with
  | mkT _ ?updateable =>
    let updateable := (eval hnf in updateable) in
    match updateable with
    | {| mkT := ?mk |} =>
      setter mk proj
    end
  end.

(* Setter provides a way to change a field given by a projection function, along
with correctness conditions that require the projected field and only the
projected field is modified. *)
Class Setter {R T} (proj: R -> T) :=
  { set: T -> R -> R;
    set_get: forall v r, proj (set v r) = v;
    set_eq: forall r, set (proj r) r = r; }.

Arguments set {R T} proj {Setter}.

Ltac SetInstance_t :=
  match goal with
  | |- @Setter ?T _ ?A => unshelve eapply Build_Setter;
                  [ get_setter T A | intros ? r; destruct r | intros r; destruct r ];
                  intros; reflexivity
  end.

Hint Extern 1 (Setter _) => SetInstance_t : typeclass_instances.

Module RecordSetNotations.
  Notation "x [ proj := v ]" := (set proj v x)
                                  (at level 8, left associativity,
                                   format "x [ proj  :=  v ]").
End RecordSetNotations.
