Require Import Automation.

Require Import ProgLang.Prog.
Require Import ProgLang.Hoare.

(* Interfaces are groups of methods with a shared level of abstraction.

A complete, usable interface consists of three logical parts:
- An API, specifying what each operation does (the types implicitly specify what
  the operations are)
- An implementation, giving a program for each operation as well as an overall recovery procedure.
- A refinement proof that shows each operation behaves as the API specifies with
  atomic behavior on crash after running the recovery procedure. This proof
  includes giving a refinement to the abstract state used to specify the API.
 *)

(* An InterfaceAPI takes [opT], a family of types for the operations. Think of
[opT] as an inductive type where the parameter specifies what the return value
of the operation should be. This inductive type will be a set of _symbols_ for
naming the methods of the API.

The type [State] gives the abstract state of the API; the semantics of each
operation will be defined in terms of how state of this type is manipulated.
 *)
Record InterfaceAPI (opT: Type -> Type) (State:Type) :=
  { op_sem: forall T, opT T -> Semantics State T; }.

Definition background_step {opT State} (bg_step: State -> State -> Prop)
           (step: forall `(op: opT T), Semantics State T) :=
  {| op_sem := fun T (op: opT T) state v state'' =>
                 exists state', bg_step state state' /\
                       step op state' v state''; |}.

(* The specification for each operation. Note that after recovery, the abstract
state is expected to be atomic. *)
Definition op_spec opT `(api: InterfaceAPI opT State) `(op: opT T) : Specification unit T unit State :=
  fun (_:unit) state =>
    {|
      pre := True;
      post :=
        fun v state' => op_sem api op state v state';
      recover :=
        fun r state' =>
          r = tt /\
          (state' = state \/
           exists v, op_sem api op state v state');
    |}.

(* An InterfaceImpl supplies concrete programs for each method defined by [opT],
as well as a single global recovery procedure. *)
Record InterfaceImpl opT :=
  { op_impl: forall T, opT T -> prog T;
    recover_impl: prog unit; }.

(* Finally, an Interface ties everything together: the parameter [api] specifies all details of how the implementation behaves, while the fields give an implementation and a refinement proof.

Of note is that in addition to every method being correct ([impl_ok]), the
recovery procedure should preserve the behavior of [Ret], namely that nothing
happens (in terms of abstract states) if the system crashes in a quiescent state
and recovers. This is guaranteed by the [ret_rec_ok] proof. *)
Record Interface opT State (api: InterfaceAPI opT State) :=
  { interface_impl: InterfaceImpl opT;
    refinement: Refinement State;
    impl_ok : forall `(op: opT T),
        prog_spec (op_spec api op)
                  (op_impl interface_impl _ op)
                  (recover_impl interface_impl)
                  refinement;
    ret_rec_ok:
      rec_noop (recover_impl interface_impl) refinement }.

(* Helper function to get the implementation of a primitive operation from an
[Interface]. *)
Definition Prim opT `{api: InterfaceAPI opT State}
           (i:Interface api)
           {T} (op: opT T) : prog T :=
  op_impl (interface_impl i) _ op.

(* TODO: this coercion works but does not keep T implicit
   see https://coq.inria.fr/bugs/show_bug.cgi?id=5527 *)
Coercion Prim : Interface >-> Funclass.
Add Printing Coercion Prim.

Generalizable Variable A.

Theorem prim_spec : forall opT `(api: InterfaceAPI opT State)
                      `(i: Interface api)
                      `(op: opT T)
                      `(spec: Specification A T unit State),
    (forall a state, pre (spec a state) ->
            forall v state', op_sem api op state v state' ->
                    post (spec a state) v state') ->
    (forall a state, pre (spec a state) ->
            recover (spec a state) tt state) ->
    (forall a state, pre (spec a state) ->
            forall v state', post (spec a state) v state' ->
                    recover (spec a state) tt state') ->
    prog_spec spec (Prim i op) (recover_impl (interface_impl i)) (refinement i).
Proof.
  intros.
  eapply prog_spec_weaken.
  eapply (impl_ok i).
  unfold spec_impl; intros.
  exists tt; simpl; intuition.
  subst; eauto.
  repeat deex; eauto.
Qed.

(* Helper to get the recovery procedure from an [Interface]. *)
Definition irec opT `(api: InterfaceAPI opT State) `(i: Interface api) : prog unit :=
  recover_impl (interface_impl i).

Lemma irec_ret_ok : forall opT `(api: InterfaceAPI opT State) `(i: Interface api),
    rec_noop (irec i) (refinement i).
Proof.
  intros.
  eapply ret_rec_ok.
Qed.

Hint Resolve irec_ret_ok.
