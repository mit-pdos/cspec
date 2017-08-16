Require Import Helpers.Helpers.
Require Import Proc.
Require Import ProcTheorems.

(** * Proof style: Refinementand Hoare Logic

 In POCS you will often use refinement to prove that an implementation (code)
 meets its specification (spec), which puts the following obligations on you:

 - You need to define one abstraction relationship between code states and spec
   states;

 - You must show what code state [w'] is produced after running a procedure that
   implements a spec operation, starting from code state [w];

 - You must show that there exists a spec state [state'] for which the
   abstraction relationship holds between [w'] and [state'], and that the spec
   operation could have reached [state'] from state [state].

 The procedure that implements the spec operation may be a program that makes
 several steps. To reason about the behavior of this procedure we use
 Hoare-style reasoning.  We require that each individual program step has a
 Crash-Hoare-Logic specification, consisting of a precondition, a post
 condition, and recovered condition.  We then chain the steps of the program
 using Hoare reasoning.  For example, to reason about a program with two steps:
 [s1;s2], we need to show that the postcondition of [s1] implies the
 precondition of [s2]. If you can prove that, then you can conclude that if the
 precondition of [s1] holds, then the postcondition of [s1;s2] is [s2]'s
 postcondition.  This style of reasoning gives us Hoare-style specification for
 [s1;s2].

 To support reasing about crashes, the spec of each procedure must also have a
 recovered condition, in addition to the traditional Hoare precondition and
 postcondition.  The recovered condition describes the state of the computer
 after it reboots.  Other than specifying the recovered condition for each
 procedure, the infrastructure mostly separates reasoning about crash-free
 execution from reasoning about crashes and recovery (i.e., repairing the system
 after a crash).  The support for reasoning about recovery is in
 [Refinement.HoareRecovery].  In [Lab1.StatDB], we ignore crashes, and thus you
 don't have to specificy a meaningful recovered condition and implement a
 recovery procedure.  For labs 2 and lab 3, you can find solutions that don't
 require any repair after a crash, and the recovery procedure is trivial (i.e.,
 do nothing).  The last lab requires repair after a crash, which will require
 understanding [Refinement.HoareRecovery].

 The rest of this file defines the infrustructure for refinement and Hoare
 reasoning. We require that each [BaseOp] in [Refinement.Proc] comes with a
 Hoare-style specification that we then chain with rules for [Bind] and [Ret],
 the two operators that [Refinement.Proc] defines to combine [BaseOp]s into
 procedure. Once we have Hoare-style spec for a procedure, we can use the same
 Hoare reasoning to chain procedures.

 This reasoning is partially automated.  Assuming there are "ok" theorems for
 [BaseOp]s and procedures, then the Ltac [step_prog] "steps" through procedures.
 For example, the proof of [add_ok] in [Lab1/StatDBImpl] consists mostly of
 repeatedly invoking [step_prog].  [Lab1/StatDBAPI] also adds [add_ok] to the
 Hint database so that "[step_prog]" can "step" through procedures that invoke
 [add].

 As a final detail, you need to reason about initialization, and, in particular,
 show that the abstraction relationship between the initial code state w and the
 initial spec state [state] holds.

 *)

(** ** Abstraction relation and composition *)

(** A LayerAbstraction is a record with one field: [abstraction], which is a
function that returns a proposition between State1 (implementation) and State2
(spec).  It specifies for which State1's and State2's the proposition holds. For
example, in StatDB lab, the spec state is a list of integers and the
implementation state is is a pair of variables.  The [abstraction] function
states what must be true of the relationship between list of integers and the
pair of variables. *)
Record LayerAbstraction State1 State2 :=
  { abstraction : State1 -> State2 -> Prop; }.

(** The constructor for [LayerAbstraction]. *)
Definition Abstraction State := LayerAbstraction world State.

(** The identity [LayerAbstraction] constructor *)
Definition IdAbstraction State : LayerAbstraction State State :=
  {| abstraction := fun state state' => state' = state; |}.

(** The following function is a constructor to compose two
[LayerAbstraction]'s. It returns an abstraction function that is the composition
of [abs1], a relation between the state of the lower layer and the state of a
middle layer, and [abs2], the relation between the state of the middle layer and
the state of the top layer. *)
Definition abstraction_compose
           `(abs1: Abstraction State1)
           `(abs2: LayerAbstraction State1 State2) :=
  {| abstraction := fun w state' => exists state, abstraction abs2 state state' /\
                                  abstraction abs1 w state; |}.

(** A Crash Hoare Logic record to express the specification of procedures. The
record has fields for the precondition, postcondition, and recovered condition
of a procedure. *)
Record Quadruple T R State :=
  Spec {
      pre: Prop;
      post: T -> State -> Prop;
      recovered: R -> State -> Prop;
    }.

(** This function is a constructor for a spec [Quadruple].  It takes as arguments a
type [A] (to be used in the precondition), a result type [T] (the type returned
by the procedure when no crashes) and a recovered type [R] (the type returned by
the recovery procedure), and a spec state ([state]), and returns a Hoare
Quadruple. *)
Definition Specification A T R State := A -> State -> Quadruple T R State.


(** ** Correctness of a program

  [prog_spec] defines when a specification holds for a procedure [p] and a
  recovery procedure [rec].  The correctness is defined in a
  refinement style.

  The general shape of what [proc_spec] says is as follows: 

<<
            pre                      post 
             |                         | 
             V                         V 
          code state --[procedure]--> state'
>>
          
  The top-level [proc_spec] statement has a precondition that maps the
  starting code state to the starting spec state, and postcondition that maps
  the final code state to the correspoding final spec state.

  The precondition takes additional argument as input, which can appear in
  postcondition.  useful for saying "if exists some abstract state in the
  precondition, then..."

  In more detail, [prog_spec] states that forall precondition arguments ([a]),
  code states ([w]), and spec states ([state]):

  - if the abstraction relation holds between code state [w] and spec state [state]

  - if the precondition holds for [a] and [state]

  - if the procedure [p] starts from code state [w] and perhaps running the recovery 
    procedure one mor more times (if there is a crash), then one of the following two 
    must be true: 

  - 1) if execution finishes without crashes in code state [w'] and returning [v],
    then there exists a spec [state'] in which the abstraction relationholds
    between [w'] and [state'] and the postcondition holds in [state'], OR

  - 2) if execution finishes in code state [w'] and returning [v] after perhaps
    several crashes and running the recovery procedure [r] several times , then
    there exists a spec [state'] in which the abstraction relation holds between
    [w'] and [state'] and the recovered condition holds in [state'].

  The [rexecution] relationship describes what a valid execution is and is
  defined in [Refinement.Proc].

 *)

Definition proc_spec `(spec: Specification A T R State) `(p: proc T)
           `(rec: proc R)
           `(abs: Abstraction State) :=
  forall a w state,
    abstraction abs w state ->
    pre (spec a state) ->
    forall r, rexec p rec w r ->
         match r with
         | RFinished v w' => exists state',
                            abstraction abs w' state' /\
                            post (spec a state) v state'
         | Recovered v w' => exists state',
                            abstraction abs w' state' /\
                            recovered (spec a state) v state'
         end.

(** Hoare-style implication: [spec1] implies [spec2] if

   - forall arguments and all states [state] for which [spec2]'s precondition
     holds

   - there exists an argument for which [spec1]'s precondition holds in [state]

   - for all states [state'] in which the postcondition of [spec1] holds, then
     the post condition of [spec2] also holds

   - for all states [state'] in which the recovered condition of [spec1] holds,
     then the recovered condition of [spec2] also holds

  *)

Definition spec_impl
           `(spec1: Specification A' T R State)
           `(spec2: Specification A T R State) :=
  forall a state, pre (spec2 a state) ->
         exists a', pre (spec1 a' state) /\
               (forall v state', post (spec1 a' state) v state' ->
                        post (spec2 a state) v state') /\
               (forall rv state', recovered (spec1 a' state) rv state' ->
                         recovered (spec2 a state) rv state').

(** Theorem for Hoare-style weakening: if [spec1] holds and [spec1] implies
[spec2], then [spec2] also holds. *)

Theorem proc_spec_weaken : forall `(spec1: Specification A T R State)
                              `(spec2: Specification A' T R State)
                              `(p: proc T) `(rec: proc R)
                              (abs: Abstraction State),
    proc_spec spec1 p rec abs ->
    spec_impl spec1 spec2 ->
    proc_spec spec2 p rec abs.
Proof.
  unfold proc_spec at 2; intros.
  eapply H0 in H2; eauto; repeat deex.
  eapply H in H3; eauto.
  destruct r; simpl in *; repeat deex; intuition eauto.
Qed.

Hint Resolve tt.

(** Theorem for the [Bind] operation: *)
Theorem proc_spec_rx : forall `(spec: Specification A T R State)
                         `(p: proc T) `(rec: proc R)
                         `(rx: T -> proc T')
                         `(spec': Specification A' T' R State)
                         `(abs: Abstraction State),
    proc_spec spec p rec abs ->
    (forall a' state, pre (spec' a' state) ->
             exists a, pre (spec a state) /\
                  (forall r,
                      proc_spec
                        (fun (_:unit) state' =>
                           {| pre := post (spec a state) r state';
                              post :=
                                fun r state'' =>
                                  post (spec' a' state) r state'';
                              recovered :=
                                fun r state'' =>
                                  recovered (spec' a' state) r state'' |})
                        (rx r) rec abs) /\
                  (forall r state', recovered (spec a state) r state' ->
                           recovered (spec' a' state) r state')) ->
    proc_spec spec' (Bind p rx) rec abs.
Proof.
  unfold proc_spec at 3; intros.
  inv_rexec.
  - inv_exec.
    match goal with
    | [ Hexec: exec p _ _ |- _ ] =>
      eapply RExec in Hexec
    end.
    eapply H0 in H2; repeat deex.
    eapply H in H9; simpl in *; safe_intuition (repeat deex; eauto).
    match goal with
    | [ Hexec: exec (rx _) _ _ |- _ ] =>
      eapply RExec in Hexec;
        eapply H3 in Hexec; eauto
    end.
  - inv_exec.
    + (* p finished, rx crashed *)
      match goal with
      | [ Hexec: exec p _ _ |- _ ] =>
        eapply RExec in Hexec
      end.
      eapply H0 in H2; repeat deex.
      eapply H in H10; simpl in *; safe_intuition (repeat deex; eauto).
      match goal with
      | [ Hexec: exec (rx _) _ _ |- _ ] =>
        eapply RExecCrash in Hexec; eauto;
          eapply H3 in Hexec; eauto
      end.
    + (* p crashed before running *)
      assert (exec p w' (Crashed w')) as Hexec by ( constructor; eauto ).
      eapply RExecCrash in Hexec; eauto.
      eapply H0 in H2; repeat deex.
      eapply H in Hexec; simpl in *; safe_intuition (repeat deex; eauto).
    + (* p crashed immediately after finishing *)
      inv_exec.
      match goal with
      | [ Hexec: exec p _ _ |- _ ] =>
        eapply RExec in Hexec
      end.
      eapply H0 in H2; repeat deex.
      eapply H in H10; simpl in *; safe_intuition (repeat deex; eauto).
      match goal with
      | [ Hexec: exec (rx _) _ _ |- _ ] =>
        apply ExecCrashEnd in Hexec;
          eapply RExecCrash in Hexec; eauto;
          eapply H3 in Hexec; eauto
      end.
    + (* p itself crashed *)
      match goal with
      | [ Hexec: exec p _ _ |- _ ] =>
        eapply RExecCrash in Hexec; eauto
      end.
      eapply H0 in H2; repeat deex.
      eapply H in H10; simpl in *; safe_intuition (repeat deex; eauto).
Qed.

(** Theorem to split a spec into the RFinished and Recovered cases: *)
Theorem spec_intros : forall `(spec: Specification A T R State)
                       `(p: proc T) `(rec: proc R)
                       `(abs: Abstraction State),
    (forall a state0,
        pre (spec a state0) ->
        proc_spec
          (fun (_:unit) state =>
             {| pre := state = state0;
                post :=
                  fun r state' => post (spec a state) r state';
                recovered :=
                  fun r state' => recovered (spec a state) r state';
             |}) p rec abs) ->
    proc_spec spec p rec abs.
Proof.
  unfold proc_spec at 2; intros.
  apply H in H1.
  eapply H1 in H2; eauto.
  simpl in *; eauto.
Qed.

Ltac spec_intros := intros; eapply spec_intros; intros.

Ltac spec_case pf :=
  eapply proc_spec_weaken; [ solve [ apply pf ] |
                             unfold spec_impl ].

Theorem spec_exec_equiv : forall `(spec: Specification A T R State)
                            (p p': proc T) `(rec: proc R)
                            `(abs: Abstraction State),
    exec_equiv p p' ->
    proc_spec spec p' rec abs ->
    proc_spec spec p rec abs.
Proof.
  unfold proc_spec; intros.
  eapply H0; eauto.
  eapply rexec_equiv; eauto.
  symmetry; auto.
Qed.

Definition rec_noop `(rec: proc R) `(abs: Abstraction State) (wipe: State -> State -> Prop) :=
  forall T (v:T),
    proc_spec
      (fun (_:unit) state =>
         {| pre := True;
            post := fun r state' => r = v /\
                             state' = state;
            recovered := fun _ state' => wipe state state'; |})
      (Ret v) rec abs.

(* for recovery proofs about pure programs *)

Theorem ret_spec : forall `(abs: Abstraction State)
                     (wipe: State -> State -> Prop)
                     `(spec: Specification A T R State)
                     (v:T) (rec: proc R),
    rec_noop rec abs wipe ->
    (forall a state, pre (spec a state) ->
            post (spec a state) v state /\
            (* TODO: is it ok for this to be for all state'? *)
            forall state', wipe state state' ->
                  forall r, recovered (spec a state) r state') ->
    proc_spec spec (Ret v) rec abs.
Proof.
  intros.
  unfold proc_spec; intros.
  eapply H in H3; simpl in *; eauto.
  eapply H0 in H2.
  destruct r; safe_intuition (repeat deex; eauto).
Qed.

Ltac monad_simpl :=
  repeat match goal with
         | |- proc_spec _ (Bind (Ret _) _) _ _ =>
           eapply spec_exec_equiv; [ apply monad_left_id | ]
         | |- proc_spec _ (Bind (Bind _ _) _) _ _ =>
           eapply spec_exec_equiv; [ apply monad_assoc | ]
         end.

(** ** Automation: step_prog

  To simplify proofs, we automate reasoning about [proc_spec]. Consider a proof
  for a [proc_spec] about "a ; b". What do we need to prove?

<<
      pre                             post 
       |                               | 
       V                               V 
     state0 --[a]--> state1 --[b]--> state2
>>

  We need to find a [proc_spec] for [a] and line up our precondition with that spec's then
  reduce to proving a [proc_spec] for b, with [a]'s post as the new pre.  Keep
  doing this repeatedly.

  There are requirements to make this plan work: 
    - can find a [proc_spec] for the [a] program 
    - can line up our current state precondition with [a]'s [proc_spec] pre

  This Ltac implements this plan.  It compares Coq's current goal  to:
  
  - [forall]: if so, intro the variables, and invoke [step_prog] again
  
  - a proc_spec with a procedure that invokes a [Ret] operation: if so, apply
    the [ret_spec] theorem to consume the [Ret].

  - a proc_spec with a procedure that sequences two operations [a] and [b] (with [Bind]): if
    so, apply the proc_spec_rx theorem to consume the [Bind]. If an "ok" theorem
    exists for the two operations [a] and [b], then "eauto" will try to apply the two
    theorems and dismiss the obligrations, if successful.

  - a proc_spec that is implied by a proc_spec that is in context: if so, apply
    the [proc_spec_weaken] theorem

 *)


Ltac step_prog :=
  match goal with
  | |- forall _, _ => intros; step_prog
  | |- proc_spec _ (Ret _) _ _ =>
    eapply ret_spec
  | |- proc_spec _ _ _ _ =>
    monad_simpl;
    eapply proc_spec_rx; [ solve [ eauto ] | ]
  | [ H: proc_spec _ ?p _ _
      |- proc_spec _ ?p _ _ ] =>
    eapply proc_spec_weaken; [ eapply H | unfold spec_impl ]
  end.



(** ** Initialization *)

(** Initialization can succeed or fail. If it fails, the computer stops. *)
Inductive InitResult :=
| Initialized
| InitFailed.

(** Run a low-level initialization first, followed by higher-level initialization. *)
Definition then_init (init1 init2: proc InitResult) : proc InitResult :=
  r <- init1;
  match r with
  | Initialized => init2
  | Failed => Ret Failed
  end.

Definition inited_any {State} (s : State) : Prop := True.

(** The spec for initialization: *)
Definition init_abstraction
           (init: proc InitResult) (rec: proc unit)
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
          recovered :=
            fun _ w' => True;
       |}) init rec (IdAbstraction world).


(** recovery is irrelevant for initialization: we only consider systems that
successfully initialize. *)
Theorem init_abstraction_any_rec : forall (init: proc InitResult)
                                   (rec rec': proc unit)
                                   `(abs: Abstraction State)
                                   (init_sem: State -> Prop),
    init_abstraction init rec abs init_sem ->
    init_abstraction init rec' abs init_sem.
Proof.
  unfold init_abstraction, proc_spec; simpl; intros.
  destruct matches; subst; eauto.
  eapply rexec_finish_any_rec in H2.
  eapply H in H2; eauto.
Qed.

(** Spec and proof for then_init *)
Theorem then_init_compose : forall (init1 init2: proc InitResult)
                              (rec rec': proc unit)
                              `(abs1: Abstraction State1)
                              `(abs2: LayerAbstraction State1 State2)
                              (init1_sem: State1 -> Prop)
                              (init2_sem: State2 -> Prop),
    init_abstraction init1 rec abs1 init1_sem ->
    proc_spec
      (fun (_:unit) state =>
         {| pre := True;
            post :=
              fun r state' => match r with
                       | Initialized =>
                         exists state'', abstraction abs2 state' state'' /\ init2_sem state''
                       | InitFailed => True
                       end;
            recovered :=
              fun _ state' => True; |}) init2 rec abs1 ->
    init_abstraction (then_init init1 init2) rec' (abstraction_compose abs1 abs2) init2_sem.
Proof.
  intros.
  eapply init_abstraction_any_rec with rec.
  unfold init_abstraction; intros.
  step_prog; intuition; simpl in *.
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
    inv_rexec; inv_exec.
    congruence.
Qed.

