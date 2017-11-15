Require Import Helpers.Helpers.
Require Import Omega.
Require Import Proc.
(* Require Import ProcTheorems. *)

(** * Specification style: Abstractions with pre- and post-conditions

 In POCS you will often write specifications that abstract away
 the state manipulated by the lower-level code into a higher-level
 representation of the state, which we will call a "spec state".
 This style of specification, for a given procedure, consists of
 two parts: (1) the type of the abstract state, and (2) a description
 of how this abstract state can change as a result of running a procedure.

 To prove that an implementation (code) meets its specification
 (spec), which puts the following obligations on you:

 - You need to define an abstraction relation that connects code
   states and spec states;

 - Whenever the code runs from state [w] to state [w'] and the abstraction
   relation holds between [w] and [state], you must show that there exists
   a spec state [state'] for which the abstraction relation holds between
   [w'] and [state'], and that the specification allows the procedure to
   change the abstract state from [state] to [state'].

 Here's a picture representing these proof obligations:

<<
                     spec semantics
     forall state ===================> exists state'
              ^                                 ^^
         absR |                            absR ||
              V   semantics of code             VV
       forall w  -----------------------> forall w'
>>

 Single lines are what the proof assumes, and double lines are what you
 must show in your proof.

 The rest of this file defines what it means to construct an abstraction
 relation between code states and spec states, what it means to define a
 specification, and how we can structure these proofs.
 *)

(** ** Abstraction relation and composition *)

(** A LayerAbstraction is a record with one field, [abstraction],
  which relates two states: one of type [State1] and another of type [State2].
  Think of [State1] as being the type of code states whereas [State2] is the
  type for specification states.  The abstraction relation links these two
  states together.

  For example, in StatDB lab, the spec state is a list of
  integers and the implementation state is is a pair of variables.  In the
  StatDB lab, the
  [abstraction] function must state what must be true of the relationship between
  the list of integers and the pair of variables.
 *)

Record LayerAbstraction State1 State2 :=
  { abstraction : State1 -> State2 -> Prop; }.

(**
  We can compose abstractions, by layering one abstraction on top
  of another.  In our case, since everything is ultimately connected
  to [world] states at the bottom, we define a composition of two
  kinds of abstraction: one that goes from [world] states to [State1],
  and another that goes from [State1] to [State2], to produce an
  abstraction from [world] to [State2].

  [abstraction_compose] makes this connection precise, by saying
  that [world] and [State2] states are connected by the fact that
  there exists some intermediate [State1] state that matches the
  two abstractions being composed.
  *)

Definition abstraction_compose
           `(abs1: LayerAbstraction State1 State2)
           `(abs2: LayerAbstraction State2 State3) :=
  {| abstraction := fun s1 s3 => exists s2,
                                  abstraction abs1 s1 s2 /\
                                  abstraction abs2 s2 s3; |}.

(**
  In some situations, we will want to keep the same level of abstraction
  (i.e., have the code and spec states be the same).  [IdAbstraction]
  defines this "identity" kind of abstraction: it is a relation between
  states of the same type [State], and the relation says that the two
  states must be equal.
 *)

Definition IdAbstraction State : LayerAbstraction State State :=
  {| abstraction := fun state state' => state' = state; |}.


(** ** Specification *)

(** Our specifications describe how a procedure can change the
  state of the system, at some level of abstraction.  We describe
  the allowed state changes using pre- and post-conditions, as
  captured by the following structure, [SpecProps].

  [SpecProps] is parametrized by three types: [T], [R], and [State].

  [State] is the type of states that this specification uses.
  For instance, in the StatDB example, [State] would be [list nat].

  [T] is the type of the return value of the procedure being
  specified.  Note that the [post] condition is a function of
  two arguments: one of type [T] (the returned value), and another
  of type [State] (the resulting state).

  In addition to pre- and post-conditions, our specifications include
  recovery conditions, which help reason about crashes during the
  execution of a procedure.  After a crash, a recovery procedure will
  run to recover any state from the crash.  The recovery procedure may
  also return some result; this result's type is [R], and the recovery
  condition, [recovered], takes two arguments: the return value from
  recovery, [R], and the state after recovery, [State].
 *)

Record SpecProps T State :=
  Spec {
    pre: Prop;
    post: T -> State -> Prop;
  }.

(**
  One obvious part missing from the [SpecProps] specification is any
  reference to the starting state.  The reason we didn't pass it as
  an argument to the precondition, [pre], is that it's useful to refer
  to the starting state inside the [post] and [recovered] conditions
  as well, in order to connect the final state to the starting state.

  Another part which is not so obviously missing is a way to talk about
  existential variables in the specification (sometimes called "ghost
  variables" in the PL literature).  This is a bit hard to
  grasp in an abstract sense; we will use this in lab 4, and it's safe
  to ignore it until then.

  We add these two missing parts to a specification by defining the
  actual type of specifications, [Specification], as a function from
  a ghost variable [A] and a starting state [State] to a [SpecProps].
  This allows the pre-, post-, and recovered conditions in [SpecProps]
  to refer to the starting state (and the ghost variable).
 *)

Definition Specification A T State := nat -> A -> State -> SpecProps T State.


(** ** Correctness of a procedure

  [proc_spec] defines when a specification holds for a procedure
  [p] and a recovery procedure [rec].  (The recovery procedure
  will become important in labs 3 and 4, when we reason about
  crashes.)  [proc_spec] formalizes our intuition of what it
  might mean to satisfy a pre- and post-condition specification.

  The general shape of what [proc_spec] says, ignoring recovery
  for now, is:

<<
            pre                      post
             |                        ||
             V                        VV
           state                    state'
             ^                        ^^
        absR |                   absR ||
             V                        VV
             w ---[procedure p]-----> w'
>>

  The single arrows indicate the assumptions (that there exists
  some starting abstract state [state], corresponding to a world
  state [w], where the precondition [pre] holds, and that running
  the procedure [p] gives us state [w'].)

  The double arrows indicate what [proc_spec] concludes: that there
  is an abstract state [state'] corresponding to [w'], and that the
  postcondition holds in that resulting state [state'].

  This picture should look familiar; it is quite similar to the
  proof obligations described at the top of this file, with the
  extra detail of how we describe the allowed transitions (namely,
  using pre- and post-conditions).

  In more detail, [proc_spec] states that for all ghost variables
  [a], starting states [w], and spec states [state]:

  - assume that the abstraction relation holds between [w] and [state]

  - assume that the precondition holds for [a] and [state]

  - if the procedure [p] starts from code state [w], then one of the
    following must be true:

    - (1) if execution finishes without crashes in code state [w'] and
      returns [v], then there exists a spec state [state'] in which the
      abstraction relation holds between [w'] and [state'] and the
      postcondition holds in [state'] with return value [v], OR

    - (2) if execution finishes in code state [w'] and returns [v]
      (after perhaps several crashes and running the recovery
      procedure [r] on each crash), then there exists a spec state
      [state'] and some return value [v] from the recovery procedure,
      in which the abstraction relation holds
      between [w'] and [state'] and the recovered condition holds in [state']
      with return value [v].

  The [rexec] relation describes how procedures execute, and
  is defined in [Spec.Proc].
 *)

Definition proc_spec `(spec: Specification A T State) `(p: proc opT T) Sem proto :=
  forall tid a state,
    pre (spec tid a state) ->
    forall r, exec Sem proto p tid state r ->
         match r with
         | Finished v s' => post (spec tid a state) v s'
         | ProtocolMismatch => False
         end.


Definition example_state := nat -> nat.

Definition example_proto :=
  fun (tid' : nat) (s0 s1 : example_state) =>
    forall tid'', tid'' <> tid' -> s0 tid'' = s1 tid''.

Definition inc (s : example_state) (tid : nat) :=
  fun x => if x == tid then (s x) + 1 else s x.

Definition dec (s : example_state) (tid : nat) :=
  fun x => if x == tid then (s x) - 1 else s x.

Inductive example_opT : Type -> Type :=
| Inc : example_opT unit
| Dec : example_opT unit.

Inductive example_op_step : forall T, example_opT T -> nat -> example_state -> T -> example_state -> Prop :=
| RunInc : forall s tid,
  example_op_step Inc tid s tt (inc s tid)
| RunDec : forall s tid,
  example_op_step Dec tid s tt (dec s tid).

Definition inc_twice := _ <- Op _ _ Inc; Op _ _ Inc.

Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import FunctionalExtensionality.

Definition inc_twice_spec : Specification _ _ _ :=
  fun (tid : nat) (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\
      exists state'',
      clos_refl_trans _ (rely example_opT example_op_step example_proto tid) state state'' /\
      state' = inc (inc state'' tid) tid;
  |}.


Lemma inc_dec_eq : forall s tid, dec (inc s tid) tid = s.
Proof.
  intros.
  apply functional_extensionality.
  unfold inc, dec; intros.
  destruct (x == tid); omega.
Qed.

Lemma inc_inc : forall s tid tid', inc (inc s tid) tid' = inc (inc s tid') tid.
Proof.
  intros.
  apply functional_extensionality.
  unfold inc, dec; intros.
  destruct (x == tid); destruct (x == tid'); omega.
Qed.

Lemma inc_dec_ne : forall s tid tid', tid <> tid' ->
  dec (inc s tid) tid' = inc (dec s tid') tid.
Proof.
  intros.
  apply functional_extensionality.
  unfold inc, dec; intros.
  destruct (x == tid); destruct (x == tid'); omega.
Qed.

Lemma example_proto_inc : forall tid s,
  example_proto tid s (inc s tid).
Proof.
  unfold example_proto, inc; intros.
  destruct (tid'' == tid); omega.
Qed.

Lemma example_proto_dec : forall tid s,
  example_proto tid s (dec s tid).
Proof.
  unfold example_proto, dec; intros.
  destruct (tid'' == tid); omega.
Qed.


Definition op_commutes T (op : example_opT T) := forall s0 s1 s2 tid r,
  example_op_step op tid s0 r s1 ->
  rely example_opT example_op_step example_proto tid s1 s2 ->
  exists s1',
  rely example_opT example_op_step example_proto tid s0 s1' /\
  example_op_step op tid s1' r s2.

Theorem inc_commutes : op_commutes Inc.
Proof.
  unfold op_commutes.
  intros.
  exists (dec s2 tid).
  unfold rely in H0. repeat deex.
  clear H1.

  destruct op'.
  - inversion H; clear H; subst; repeat sigT_eq.
    inversion H2; clear H2; subst; repeat sigT_eq.

    rewrite inc_dec_ne by eauto.
    rewrite inc_dec_eq.
    rewrite inc_inc.

    intuition.
    + unfold rely. do 4 eexists; intuition eauto.
      apply example_proto_inc.
      constructor.

    + constructor.

  - inversion H; clear H; subst; repeat sigT_eq.
    inversion H2; clear H2; subst; repeat sigT_eq.

    rewrite inc_dec_ne by eauto.
    rewrite inc_dec_eq.

    intuition.
    + unfold rely. do 4 eexists; intuition eauto.
      apply example_proto_dec.
      constructor.

    + constructor.
Qed.

Theorem op_commutes_star : forall T (op : example_opT T) r s0 s1 s2 tid,
  op_commutes op ->
  example_op_step op tid s0 r s1 ->
  clos_refl_trans example_state
       (rely example_opT example_op_step example_proto tid) 
       s1 s2 ->
  exists s1',
  clos_refl_trans example_state
       (rely example_opT example_op_step example_proto tid) 
       s0 s1' /\
  example_op_step op tid s1' r s2.
Proof.
  intros.
  apply Operators_Properties.clos_rt_rt1n in H1.
  generalize dependent s0.
  induction H1; intros.
  - exists s0. intuition eauto. apply rt_refl.
  - edestruct H; intuition eauto.
    edestruct IHclos_refl_trans_1n; intuition eauto.
    eexists; intuition eauto.
    eapply rt_trans.
    constructor; eauto.
    eauto.
Qed.


Theorem inc_twice_ok : proc_spec inc_twice_spec inc_twice example_op_step example_proto.
Proof.
  unfold proc_spec, inc_twice_spec, inc_twice.
  simpl.
  intros.

  apply exec_exec2_equiv in H0.
  destruct r.

  - inversion H0; clear H0; subst; repeat sigT_eq.
    inversion H7; clear H7; subst; repeat sigT_eq.
    inversion H9; clear H9; subst; repeat sigT_eq.

    inversion H8; subst; repeat sigT_eq.
    inversion H11; subst; repeat sigT_eq.

    clear H10.
    clear H12.

    intuition eauto.

    edestruct op_commutes_star.
    apply inc_commutes.
    apply H8.
    apply H5.
    clear H8.
    clear H5.
    intuition.

    eexists; intuition idtac.
    eapply rt_trans; eauto.

    inversion H2; clear H2; subst; repeat sigT_eq.
    reflexivity.

  - inversion H0; subst; repeat sigT_eq.
    + inversion H7; subst; repeat sigT_eq.
      inversion H9; subst; repeat sigT_eq.
      inversion H3; subst; repeat sigT_eq.
      apply H6.

      unfold example_proto; intros.
      unfold inc.
      destruct (tid'' == tid).
      congruence.
      congruence.

    + inversion H7; subst; repeat sigT_eq.
      inversion H3; subst; repeat sigT_eq.
      apply H5.

      unfold example_proto; intros.
      unfold inc.
      destruct (tid'' == tid).
      congruence.
      congruence.
Qed.



(** ** Proving correctness *)

(** To help us construct proofs about procedures satisfying
  a specification, it helps to have a notion of when one
  specification implies another specification.  Here, we
  define what it means for [spec1] to imply [spec2] (the
  two specifications must be at the same level of abstraction
  and must talk about the same types of return values):

   - for all ghost variables and all states [state] for which [spec2]'s
     precondition holds,

   - there exists a ghost variable for which [spec1]'s precondition
     holds in [state]

   - for all states [state'] in which the postcondition of [spec1]
     holds, then the post condition of [spec2] also holds

   - for all states [state'] in which the recovered condition of
     [spec1] holds, then the recovered condition of [spec2] also holds.
  *)

Definition spec_impl
           `(spec1: Specification A' T State)
           `(spec2: Specification A T State) :=
  forall a state, pre (spec2 a state) ->
         exists a', pre (spec1 a' state) /\
               (forall v state', post (spec1 a' state) v state' ->
                        post (spec2 a state) v state').

(** We now prove that the above definition of what it means for
  one specification to imply another one is actually correct.
  This means that, if a procedure satisfies [spec1], and [spec1]
  implies [spec2], then the same procedure must also satisfy [spec2].
 *)

Theorem proc_spec_weaken : forall `(spec1: Specification A T State)
                              `(spec2: Specification A' T State)
                              `(p: proc opT T) Sem,
    proc_spec spec1 p Sem ->
    spec_impl spec1 spec2 ->
    proc_spec spec2 p Sem.
Proof.
  unfold proc_spec at 2; intros.
  eapply H0 in H1; eauto; repeat deex.
  eapply H in H2; eauto.
  destruct r; simpl in *; repeat deex; intuition eauto.
Qed.

Hint Resolve tt.

(** This is a crucial step for constructing proofs of correctness.
  We will decompose proofs about a [Bind] operation (i.e.,
  combining two procedures, [p] and [rx], with a semicolon) into
  smaller proofs about the individual procedures [p] and [rx].

  Specifically, in order to prove that [p; rx] satisfies [spec'],
  it suffices to have some specification [spec] for [p], and to
  prove that the precondition of [spec'] implies the precondition
  of [spec], and that [rx] meets a specification that, informally,
  fixes up the postcondition of [spec] to match the postcondition
  of [spec'].

  More precisely:
 *)

Theorem proc_spec_rx : forall `(spec: Specification A T State)
                         `(p: proc opT T)
                         `(rx: T -> proc opT T')
                         `(spec': Specification A' T' State)
                         Sem,
    proc_spec spec p Sem ->
    (forall a' state, pre (spec' a' state) ->
             exists a, pre (spec a state) /\
                  (forall r,
                      proc_spec
                        (fun (_:unit) state' =>
                           {| pre := post (spec a state) r state';
                              post :=
                                fun r state'' =>
                                  post (spec' a' state) r state'' |})
                        (rx r) Sem)) ->
    proc_spec spec' (Bind p rx) Sem.
Proof.
  unfold proc_spec at 3; intros.
  inv_exec.
  edestruct H0; eauto.
  intuition.
  eapply H in H8; eauto.
  eapply H4 in H10; simpl; eauto.
Qed.


(** In some situations, the precondition of a specification
  may define variables or facts that you want to [intros].
  Here we define several helper theorems and an Ltac tactic, [spec_intros],
  that does so.  This is done by changing the specification's precondition
  from an arbitrary Prop (i.e., [pre]) into a statement that there's
  some state [state0] such that [state = state0], and [intros]ing the
  arbitrary Prop in question as a hypothesis about [state0].
*)

Theorem spec_intros : forall `(spec: Specification A T State)
                       `(p: proc opT T)
                       Sem,
    (forall a state0,
        pre (spec a state0) ->
        proc_spec
          (fun (_:unit) state =>
             {| pre := state = state0;
                post :=
                  fun r state' => post (spec a state) r state';
             |}) p Sem) ->
    proc_spec spec p Sem.
Proof.
  unfold proc_spec at 2; intros.
  apply H in H0.
  eapply H0 in H1; eauto.
  simpl in *; eauto.
Qed.

Ltac spec_intros := intros; eapply spec_intros; intros.

Ltac spec_case pf :=
  eapply proc_spec_weaken; [ solve [ apply pf ] |
                             unfold spec_impl ].

(** Finally, we prove that our notion of equivalent procedures,
  [exec_equiv], is actually correct: if [p] and [p'] are equivalent,
  then they meet the same specifications.

  We will use this next to reason about procedure transformations
  that shouldn't change the behavior of a procedure.
 *)

Theorem spec_exec_equiv : forall opT `(spec: Specification A T State)
                            (p p': proc opT T)
                            Sem,
    exec_equiv Sem p p' ->
    proc_spec spec p' Sem ->
    proc_spec spec p Sem.
Proof.
  unfold proc_spec; intros.
  eapply H0; eauto.
  apply H. eauto.
Qed.


(** A more general theorem about specifications for [Ret], which
  we will use as part of our proof automation, says
  that [Ret v] meets a specification [spec] if the [rec_noop]
  theorem holds (i.e., the recovery procedure is correctly
  described by a wipe relation [wipe]), and the specification
  [spec] matches the [wipe] relation:
 *)

Theorem ret_spec : forall opT
                     `(spec: Specification A T State)
                     (v:T) Sem,
    (forall a state, pre (spec a state) ->
            post (spec a state) v state) ->
    proc_spec spec (@Ret opT T v) Sem.
Proof.
  intros.
  unfold proc_spec; intros.
  eapply H in H0; simpl in *; eauto.
  inv_exec. destruct r.
  intuition subst.
  eauto.
Qed.

(** ** Proof automation

  We will now define some Ltac tactics to help us prove
  the correctness of procedures.  We start with a simple
  tactic that will eliminate unnecessary [Ret] return
  statements and will re-order semicolons into a consistent
  order.

  This tactic, [monad_simpl], makes use of the [monad_left_id]
  and [monad_assoc] theorems to manipulate procedures, simplifying
  their return statements and semicolons, together with the theorem
  we proved above, [spec_exec_equiv], about specifications of
  equivalent procedures.
 *)

Ltac monad_simpl :=
  repeat match goal with
         | |- proc_spec _ (Bind (Ret _) _) _ _ =>
           eapply spec_exec_equiv; [ apply monad_left_id | ]
         | |- proc_spec _ (Bind (Bind _ _) _) _ _ =>
           eapply spec_exec_equiv; [ apply monad_assoc | ]
         end.

(** ** step_proc

  To simplify proofs, we automate reasoning about [proc_spec].
  Consider a proof for a [proc_spec] about "a ; b". What do
  we need to prove?

<<
      pre                             post
       |                               |
       V                               V
     state0 --[a]--> state1 --[b]--> state2
>>

  We need to find a [proc_spec] for [a] and line up our precondition with
  that spec's, then reduce to proving a [proc_spec] for b, with [a]'s post
  as the new pre.  Keep doing this repeatedly.

  There are two requirements to make this plan work:
    - a [proc_spec] for the [a] procedure
    - a way to line up our current state's precondition with
      [a]'s [proc_spec] precondition

  The following Ltac, [step_proc], implements this plan.
  It compares Coq's current goal to:

  - a [proc_spec] with a procedure that invokes a [Ret] operation:
    if so, apply the [ret_spec] theorem to consume the [Ret].  This
    will generate some proof obligations, corresponding to the premises
    of the [ret_spec] theorem.

  - a [proc_spec] with a procedure that sequences two operations [a] and [b]
    (with [Bind]): if so, apply the [proc_spec_rx] theorem to consume the
    [Bind].  This will generate some proof obligations, corresponding to
    the premises of the [proc_spec_rx] theorem.

    A common pattern is that we have already proven that [a] already meets
    some specification.  To automate this case, [step_proc] calls [eauto]
    to find such a theorem.  We tell Coq about these theorems using
    [Hint Resolve] statements that you will see throughout our lab code.

    Proving the correctness of the [b] procedure will remain as a proof
    obligation.

  - a [proc_spec] that is implied by a [proc_spec] that is already in
    context: if so, apply the [proc_spec_weaken] theorem and try to
    prove that one spec implies the other.
 *)

Check proc_spec.

Ltac step_proc_basic :=
  match goal with
  | |- forall _, _ => intros; step_proc_basic
  | |- proc_spec _ (Ret _) _ =>
    eapply ret_spec
  | |- proc_spec _ _ _ =>
    monad_simpl;
    eapply proc_spec_rx; [ solve [ eauto ] | ]
  | [ H: proc_spec _ ?p _
      |- proc_spec _ ?p _ ] =>
    eapply proc_spec_weaken; [ eapply H | unfold spec_impl ]
  end.

Ltac step_proc :=
  intros;
  match goal with
  | |- proc_spec _ (Ret _) _ =>
    eapply ret_spec
  | |- proc_spec _ _ _ =>
    monad_simpl;
    eapply proc_spec_rx; [ solve [ eauto ] | ]
  | [ H: proc_spec _ ?p _ _
      |- proc_spec _ ?p _ _ ] =>
    eapply proc_spec_weaken; [ eapply H | unfold spec_impl ]
  end;
  intros; simpl;
  cbn [pre post] in *;
  repeat match goal with
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ |- forall _, _ ] => intros
         | [ |- exists (_:unit), _ ] => exists tt
         | [ |- _ /\ _ ] => split; [ solve [ trivial ] | ]
         | [ |- _ /\ _ ] => split; [ | solve [ trivial ] ]
         | _ => solve [ trivial ]
         | _ => progress subst
         | _ => progress autounfold in *
         end.

(** ** Initialization

  Initialization is special because, when the initialization
  procedure starts running, the system may be in a
  state that does not correspond to ANY abstract state yet.
  This means that we will need to write a stylized kind of
  specification about initialization procedures.

  As a common pattern, initialization can succeed or fail.
  If it fails, we typically do not promise anything.
 *)

(*
Inductive InitResult :=
| Initialized
| InitFailed.

(** When we compose multiple layers together, a common pattern
  that emerges is trying to initialize the lower level first,
  and then initializing the higher level.  The reason we don't
  just combine the procedures using semicolon (i.e., [Bind])
  is that if the lower-level initialization fails, we should
  return failure right away, instead of continuing to run the
  higher-level initialization.
 *)

Definition then_init (init1 init2: proc InitResult) : proc InitResult :=
  r <- init1;
  match r with
  | Initialized => init2
  | Failed => Ret Failed
  end.

(** ** Initialization specs

  To specify what it means for the initialization procedure to
  be correct, it suffices to simply write a predicate describing
  the initialized states that will be produced by the initialization
  procedure.  A common description of these states is "any state
  that satisfies the abstraction relation", which we can define
  using [inited_any]:
 *)

Definition inited_any `(s : State) : Prop := True.

(** We define this shorthand for the specification of an initialization
  procedure.  Given a description of the states that initialization
  should produce (e.g., [inited_any] above), [init_abstraction] produces
  a full-fledged pre- and post-condition-style specification, which
  says that, if initialization returns success, the resulting state
  is one of the allowed states:
 *)

Definition init_abstraction
           (init: proc InitResult)
           `(abs: Abstraction State) (init_sem: State -> Prop) :=
  proc_spec
    (fun (_:unit) w =>
       {| pre := True;
          post :=
            fun r w' => match r with
                     | Initialized =>
                       exists state, abstraction abs w' state /\ init_sem state
                     | InitFailed => True
                     end;
       |}) init (IdAbstraction world).

(** Since the [init_abstraction] specification above does not
  place any requirements in case we crash during initialization,
  the specific recovery procedure doesn't matter:
 *)

Theorem init_abstraction_any_rec : forall (init: proc InitResult)
                                   `(abs: Abstraction State)
                                   (init_sem: State -> Prop),
    init_abstraction init abs init_sem ->
    init_abstraction init abs init_sem.
Proof.
  unfold init_abstraction, proc_spec; simpl; intros.
  destruct matches; subst; eauto.
Admitted.

(** Finally, we prove a specialized theorem about how to compose
  two initialization procedures using the [then_init] composition
  operator defined above:
 *)

Theorem then_init_compose : forall (init1 init2: proc InitResult)
                              `(abs1: Abstraction State1)
                              `(abs2: LayerAbstraction State1 State2)
                              (init1_sem: State1 -> Prop)
                              (init2_sem: State2 -> Prop),
    init_abstraction init1 abs1 init1_sem ->
    proc_spec
      (fun (_:unit) state =>
         {| pre := init1_sem state;
            post :=
              fun r state' => match r with
                       | Initialized =>
                         exists state'', abstraction abs2 state' state'' /\ init2_sem state''
                       | InitFailed => True
                       end; |}) init2 abs1 ->
    init_abstraction (then_init init1 init2) (abstraction_compose abs1 abs2) init2_sem.
Proof.
  intros.
  unfold init_abstraction; intros.
  step_proc; intuition; simpl in *.
  descend; intuition eauto.
  destruct r.
  - clear H.
    unfold proc_spec in *; (intuition eauto); simpl in *;
      subst; repeat deex.
    eapply H in H3; eauto.
    destruct matches in *; safe_intuition (repeat deex; eauto).
    descend; intuition eauto.
  - unfold proc_spec; simpl; intros.
    destruct matches; subst; eauto.
    eexists; intuition eauto.
    inv_exec.
    congruence.
Qed.
*)

Definition spec_lower `(s : Specification A T State) `(abs : LayerAbstraction LState State) : Specification _ T LState :=
  fun '(a, remember_state) lstate =>
    {|
      pre := exists state, abstraction abs lstate state /\ pre (s a state) /\ remember_state = state;
      post := fun r lstate' =>
        exists state', abstraction abs lstate' state' /\ post (s a remember_state) r state';
    |}.
