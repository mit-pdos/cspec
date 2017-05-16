Require Import Automation.

Require Import ProgLang.Prog.
Require Import ProgLang.Hoare.
Require Import ProgLang.HoareRecovery.

Record InterfaceAPI opT State :=
  { op_sem: forall T, opT T -> Semantics State T; }.

Definition background_step {opT State} (bg_step: State -> State -> Prop)
           (step: forall `(op: opT T), Semantics State T) :=
  {| op_sem := fun T (op: opT T) state v state'' =>
                 exists state', bg_step state state' /\
                       step op state' v state''; |}.

Definition op_spec opT `(api: InterfaceAPI opT State) `(op: opT T) : RecSpecification unit T unit State :=
  fun (_:unit) state =>
    {|
      rec_pre := True;
      rec_post :=
        fun v state' => op_sem api op state v state';
      recover_post :=
        fun r state' =>
          r = tt /\
          (state' = state \/
           exists v, op_sem api op state v state');
    |}.

Record InterfaceImpl opT :=
  { op_impl: forall T, opT T -> prog T;
    recover_impl: prog unit; }.

Record Interface opT State (api: InterfaceAPI opT State) :=
  { interface_impl: InterfaceImpl opT;
    refinement: Refinement State;
    impl_ok : forall `(op: opT T),
        prog_rspec (op_spec api op)
                   (op_impl interface_impl _ op)
                   (recover_impl interface_impl)
                   refinement; }.

Definition Prim opT `{api: InterfaceAPI opT State}
           (i:Interface api)
           {T} (op: opT T) : prog T :=
  op_impl (interface_impl i) _ op.

(* TODO: this coercion works but does not keep T implicit
   see https://coq.inria.fr/bugs/show_bug.cgi?id=5527 *)
Coercion Prim : Interface >-> Funclass.
Add Printing Coercion Prim.

Theorem prim_ok : forall opT `(api: InterfaceAPI opT State)
                    `(i: Interface api)
                    `(op: opT T)
                    `(spec: RecSpecification A T unit State),
    (forall a state, rec_pre (spec a state) ->
            forall v state', op_sem api op state v state' ->
                    rec_post (spec a state) v state') ->
    (forall a state, rec_pre (spec a state) ->
            recover_post (spec a state) tt state) ->
    (forall a state, rec_pre (spec a state) ->
            forall v state', rec_post (spec a state) v state' ->
                    recover_post (spec a state) tt state') ->
    prog_rspec spec (Prim i op) (recover_impl (interface_impl i)) (refinement i).
Proof.
  intros.
  eapply prog_rspec_weaken.
  eapply (impl_ok i).
  unfold rspec_impl; intros.
  exists tt; simpl; intuition.
  subst; eauto.
  repeat deex; eauto.
Qed.
