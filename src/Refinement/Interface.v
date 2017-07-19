Require Import Automation.

Require Import Refinement.Prog.
Require Import Refinement.Hoare.
Require Import Refinement.ProgTheorems.

(**
 * Interfaces are groups of methods with a shared level of abstraction.
 *
 * A complete, usable interface consists of three logical parts:
 * - An API, specifying what each operation does (the types implicitly
 *   specify what the operations are)
 * - An implementation, giving a program for each operation as well as
 *   an overall recovery procedure.
 * - A refinement proof that shows each operation behaves as the API
 *   specifies with atomic behavior on crash after running the recovery
 *   procedure. This proof includes giving an abstraction to the abstract
 *   state used to specify the API.
 *)

(* An InterfaceAPI takes [opT], a family of types for the operations. Think of
[opT] as an inductive type where the parameter specifies what the return value
of the operation should be. This inductive type will be a set of _symbols_ for
naming the methods of the API.

The type [State] gives the abstract state of the API; the semantics of each
operation will be defined in terms of how state of this type is manipulated.
 *)
Record InterfaceAPI (opT: Type -> Type) (State:Type) :=
  {
    op_sem: forall T, opT T -> Semantics State T;
    crash_effect: State -> State -> Prop;
    init_sem: State -> Prop;
  }.

Definition pre_step {opT State}
           (bg_step: State -> State -> Prop)
           (step: forall `(op: opT T), Semantics State T) :
  forall T (op: opT T), Semantics State T :=
  fun T (op: opT T) state v state'' =>
    exists state', bg_step state state' /\
          step op state' v state''.

Definition post_step {opT State}
           (step: forall `(op: opT T), Semantics State T)
           (bg_step: State -> State -> Prop) :
  forall T (op: opT T), Semantics State T :=
  fun T (op: opT T) state v state'' =>
    exists state', step op state v state' /\
          bg_step state' state''.

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
          (crash_effect api state state' \/
           exists state1 v, op_sem api op state v state1 /\
                       crash_effect api state1 state');
    |}.

Inductive InitResult := Initialized | InitFailed.

(* An InterfaceImpl supplies concrete programs for each method defined by [opT],
as well as a single global recovery procedure.

 TODO: add documentation throughout for initialization
 *)
Record InterfaceImpl opT :=
  { op_impl: forall T, opT T -> prog T;
    recover_impl: prog unit;
    init_impl: prog InitResult; }.

Definition init_invariant
           (init: prog InitResult) (rec: prog unit)
           `(abs: Abstraction State) (init_sem: State -> Prop) :=
  prog_spec
    (fun (_:unit) w =>
       {| pre := True;
          post :=
            fun r w' => match r with
                     | Initialized =>
                       exists state, abstraction abs w' state /\ init_sem state
                     | InitFailed => True
                     end;
          recover :=
            fun _ w' => True;
       |}) init rec (IdAbstraction world).

(**
 * Finally, an Interface ties everything together: the parameter [api] specifies
 * all details of how the implementation behaves, while the fields give an
 * implementation and a refinement proof.
 *
 * Of note is that in addition to every method being correct ([impl_ok]), the
 * recovery procedure should preserve the behavior of [Ret], namely that nothing
 * happens (in terms of abstract states) if the system crashes in a quiescent state
 * and recovers. This is guaranteed by the [ret_rec_ok] proof.
 *)
Record Interface opT State (api: InterfaceAPI opT State) :=
  { interface_impl: InterfaceImpl opT;
    interface_abs: Abstraction State;
    impl_ok : forall `(op: opT T),
        prog_spec (op_spec api op)
                  (op_impl interface_impl _ op)
                  (recover_impl interface_impl)
                  interface_abs;
    ret_rec_ok:
      rec_noop (recover_impl interface_impl) interface_abs (crash_effect api);
    init_ok:
      init_invariant
        (init_impl interface_impl) (recover_impl interface_impl)
        interface_abs (init_sem api); }.

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
            forall state',
              crash_effect api state state' ->
              recover (spec a state) tt state') ->
    (forall a state, pre (spec a state) ->
            forall v state', post (spec a state) v state' ->
                    forall state'',
                      crash_effect api state' state'' ->
                      recover (spec a state) tt state'') ->
    prog_spec spec (Prim i op) (recover_impl (interface_impl i)) (interface_abs i).
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
    rec_noop (irec i) (interface_abs i) (crash_effect api).
Proof.
  intros.
  eapply ret_rec_ok.
Qed.

Hint Resolve irec_ret_ok.

(* Helpers for initialization *)

Definition iInit opT `{api: InterfaceAPI opT State} `(i: Interface api) : prog InitResult :=
  init_impl (interface_impl i).

Definition then_init (init1 init2: prog InitResult) : prog InitResult :=
  r <- init1;
    match r with
    | Initialized => init2
    | Failed => Ret Failed
    end.

Theorem init_invariant_any_rec : forall (init: prog InitResult)
                                   (rec rec': prog unit)
                                   `(abs: Abstraction State)
                                   (init_sem: State -> Prop),
    init_invariant init rec abs init_sem ->
    init_invariant init rec' abs init_sem.
Proof.
  unfold init_invariant, prog_spec; simpl; intros.
  destruct matches; subst; eauto.
  eapply rexec_finish_any_rec in H2.
  eapply H in H2; eauto.
Qed.

Theorem iInit_init_ok : forall opT `(api: InterfaceAPI opT State) `(i: Interface api),
    init_invariant (iInit i) (irec i) (interface_abs i) (init_sem api).
Proof.
  intros.
  eapply init_ok.
Qed.

Hint Resolve iInit_init_ok.

Theorem then_init_compose : forall (init1 init2: prog InitResult)
                              (rec rec': prog unit)
                              `(abs1: Abstraction State1)
                              `(abs2: LayerAbstraction State1 State2)
                              (init1_sem: State1 -> Prop)
                              (init2_sem: State2 -> Prop),
    init_invariant init1 rec abs1 init1_sem ->
    prog_spec
      (fun (_:unit) state =>
         {| pre := True;
            post :=
              fun r state' => match r with
                       | Initialized =>
                         exists state'', abstraction abs2 state' state'' /\ init2_sem state''
                       | InitFailed => True
                       end;
            recover :=
              fun _ state' => True; |}) init2 rec abs1 ->
    init_invariant (then_init init1 init2) rec' (abstraction_compose abs1 abs2) init2_sem.
Proof.
  intros.
  eapply init_invariant_any_rec with rec.
  unfold init_invariant, then_init in *; intros.
  step_prog; intuition; simpl in *.
  descend; intuition eauto.
  destruct r.
  - clear H.
    unfold prog_spec in *; (intuition eauto); simpl in *;
      subst; repeat deex.
    eapply H in H3; eauto.
    destruct matches in *; safe_intuition (repeat deex; eauto).
    descend; intuition eauto.
  - unfold prog_spec; simpl; intros.
    destruct matches; subst; eauto.
    inv_rexec; inv_exec.
    congruence.
Qed.

Ltac exec_step :=
  match goal with
    | H: exec (Prim _ _) _ _ |- _ => eapply RExec in H
    | H: exec (if ?cond then _ else _) _ _ |- _ => destruct cond
    | H: exec (match ?expr with _ => _ end) _ _ |- _ => case_eq expr; intros; subst; simpl in *
    | H: rexec _ _ _ _ |- _ => eapply impl_ok in H; [ | eassumption | solve [ simpl; eauto ] ]
    end || inv_ret || inv_exec.

Ltac exec_steps :=
  repeat exec_step;
  simpl in *; unfold pre_step in *; repeat deex.
