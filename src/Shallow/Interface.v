Require Import ProgLang.Prog.
Require Import ProgLang.Hoare.

Record InterfaceAPI opT State :=
  { op_sem: forall T, opT T -> Semantics State T; }.

Definition background_step {opT State} (bg_step: State -> State -> Prop)
           (step: forall `(op: opT T), Semantics State T) :=
  {| op_sem := fun T (op: opT T) state v state'' =>
                 exists state', bg_step state state' /\
                       step op state' v state''; |}.

Record InterfaceImpl opT :=
  { op_impl: forall T, opT T -> prog T;
    (* TODO: add a recovery procedure here *) }.

(* TODO: as with Interpret, this crash spec is nice and all but we really want a
recovery specification (even for the replicated disk). This also op_spec will
need to depend on both InterfaceAPI and InterfaceImpl (unfortunately). *)

Definition op_spec opT `(api: InterfaceAPI opT State) `(op: opT T) : Specification unit T State :=
  fun (_:unit) state =>
    {|
      pre := True;
      post :=
        fun v state' => op_sem api op state v state';
      crash :=
        fun state' =>
          state' = state;
    |}.

Record Interface opT State (api: InterfaceAPI opT State) :=
  { interface_impl: InterfaceImpl opT;
    refinement: Refinement State;
    impl_ok : forall `(op: opT T),
        (* TODO: this atomicity spec is too hard to provide, should prove a
        prog_rok wrt the implementation recovery procedure *)
        prog_ok (op_spec api op)
                (op_impl interface_impl _ op)
                refinement; }.

Definition get_op opT `{api: InterfaceAPI opT State}
           (i:Interface api)
           {T} (op: opT T) : prog T :=
  op_impl (interface_impl i) _ op.

(* TODO: this coercion works but does not keep T implicit
   see https://coq.inria.fr/bugs/show_bug.cgi?id=5527 *)
Coercion get_op : Interface >-> Funclass.
Add Printing Coercion get_op.
