Require Import ProgLang.Prog.
Require Import ProgLang.Hoare.

Record InterfaceAPI opT State :=
  { op_sem: forall T, opT T -> Semantics State T; }.

Record InterfaceImpl opT :=
  { get_op: forall T, opT T -> prog T;
    (* TODO: add a recovery procedure here *) }.

Arguments get_op {opT} impl {T} op : rename.

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
          state' = state \/
          exists v, op_sem api op state v state';
    |}.

Record Interface opT State (api: InterfaceAPI opT State) :=
  { interface_impl: InterfaceImpl opT;
    refinement: Refinement State;
    impl_ok : forall `(op: opT T),
        (* TODO: this atomicity spec is too hard to provide, should prove a
        prog_rok wrt the implementation recovery procedure *)
        prog_ok (op_spec api op)
                (get_op interface_impl op)
                refinement; }.
