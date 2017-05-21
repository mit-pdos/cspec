Require Import Automation.

Require Import ProgLang.Prog.
Require Import ProgLang.Hoare.
Require Import ProgLang.HoareRecovery.

Require Import ProgLang.ProgTheorems.

Record InterfaceAPI opT State :=
  { op_sem: forall T, opT T -> Semantics State T; }.

Definition background_step {opT State} (bg_step: State -> State -> Prop)
           (step: forall `(op: opT T), Semantics State T) :=
  {| op_sem := fun T (op: opT T) state v state'' =>
                 exists state', bg_step state state' /\
                       step op state' v state''; |}.

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
                   refinement;
    (* TODO: rec_noop is a poor name, at least for the layer proof; it's really
       a [Ret_rok] proof, showing [Ret] is correctly recovered (that is, by not
       doing anything). *)
    rec_noop_ok:
      rec_noop (recover_impl interface_impl) refinement }.

Definition Prim opT `{api: InterfaceAPI opT State}
           (i:Interface api)
           {T} (op: opT T) : prog T :=
  op_impl (interface_impl i) _ op.

(* TODO: this coercion works but does not keep T implicit
   see https://coq.inria.fr/bugs/show_bug.cgi?id=5527 *)
Coercion Prim : Interface >-> Funclass.
Add Printing Coercion Prim.

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

(* weaker version of prim_ok that requires the postcondition imply the recovery
postcondition *)
Theorem prim_ok : forall opT `(api: InterfaceAPI opT State)
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
    prog_rok spec (Prim i op) (recover_impl (interface_impl i)) (refinement i).
Proof.
  eauto using prog_rspec_to_rok, prim_spec.
Qed.

Definition irec opT `(api: InterfaceAPI opT State) `(i: Interface api) : prog unit :=
  recover_impl (interface_impl i).

Lemma irec_noop : forall opT `(api: InterfaceAPI opT State) `(i: Interface api),
    rec_noop (irec i) (refinement i).
Proof.
  intros.
  eapply rec_noop_ok.
Qed.
