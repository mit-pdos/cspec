Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import ClassicalFacts.
Require Import Helpers.Helpers.

Axiom EM : excluded_middle.

Global Set Implicit Arguments.
Global Generalizable All Variables.

(** * Model of sequential procedures with mutable state.

    In our labs, we want to reason about procedures that have side-effects,
    such as modifying the contents of memory or writing to disk.  This is
    in contrast to the kinds of procedures that one can naturally write in
    Coq's Gallina language, which are purely functional; they have no
    built-in notion of mutable state.

    To reason about procedures that manipulate mutable state,
    we need to construct an explicit Coq model of:

    - What a procedure looks like.
    - How a procedure executes.

    Our procedures will eventually be extracted from Coq into Haskell, and
    execute as Haskell programs (by compiling their Coq-generated Haskell
    source code using a Haskell compiler to produce an executable binary).

    First, we need a type to represent procedures, which will be an inductive type
    [proc] after some preliminaries. This type is a generic model of sequential
    procedures, allowing chaining procedures together. We will implement some basic
    operations in Haskell to do I/O where needed and, using extraction, link our procedures with the
    Haskell primitives and run them.

  *)

(** Our minimal, generic model of sequential procedures.

    The only detail we expose about our opaque procedures is that it's possible
    to combine procedures together, using [Ret] and [Bind]. If you're familiar
    with Haskell, these are the same as [return] and [(>>=)] for the [IO] monad.

    Procedures are parametrized by type [T], which is the type of value
    that will be returned by the procedure.  For example, a procedure
    that returns a [nat] has type [proc nat], and a procedure that returns
    nothing ("void", in C terminology) has type [proc unit].

    As a technical detail, we include a constructor [BaseOp] to include
    arbitrary external operations. Without this constructor, Coq would think
    that every [proc] consists only of [Ret] and [Bind] and thus can't have side
    effects.
  *)

Section Proc.

Variable opT : Type -> Type.

CoInductive proc (T : Type) : Type :=
| Op (op : opT T)
| Ret (v : T)
| Bind (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T).


(** Here we connect our definition of the procedure language, [proc],
    to Haskell's built-in implementations of [Bind] and [Ret], which are
    [return] and [(>>=)] respectively.  We instruct Coq to extract any
    use of [BaseOp] to an error expression, since we do not expect any
    legitimate use of [BaseOp] in Gallina.  We also instruct Coq to
    extract any attempts to pattern-match a procedure to an error, since
    we do not expect any legitimate code to pattern-match the contents of
    a [proc] procedure.
  *)

(*
Require Extraction.
Extraction Language Haskell.

Extract Inductive proc => "Proc"
                           ["error 'accessing BaseOp'" "return" "(>>=)"]
                           "(\fprim fret fbind -> error 'pattern match on proc')".
*)


(** * Execution model.

    Next, we define our model of execution.

    The model will specify how Bind chains operations together. Importantly, our
    semantics will allow a [proc] to execute to a crashed state at any any
    intermediate point in its execution. Later we'll also bring recovery
    execution into this picture.

  *)

(** When we define how procedures execute, we will say they manipulate some state
    of this opaque type [world]. We won't ever define this type in Coq, but it will
    show up later to capture the idea that procedures move from one world state to
    another in sequence.

 *)

Variable State : Type.


(** We start by defining the possible outcomes of executing a procedure [proc
    T]: either the procedure finishes and returns something of type T, or the
    procedure crashes. Because we are explicitly modeling the effect of
    procedures on the state of our system, both of these outcomes also include
    the resulting world state.
*)

Inductive Result T :=
| Finished (v:T) (s:State)
| ProtocolMismatch.

Arguments ProtocolMismatch {T}.

(*
Arguments Crashed {T} w.
*)

(** To define the execution of procedures, we need to state an axiom about how our
    opaque [baseOpT] primitives execute. This axiom is [base_step]. This is
    just another technicality.
  *)

Variable op_step : forall T, opT T -> nat -> State -> T -> State -> Prop.

(** Finally, we define the [exec] relation to represent the execution semantics
    of a procedure, leveraging the [step] and [world_crash] definitions from
    above. The interpretation is that when [exec p w r] holds, procedure [p]
    when executed in state [w] can end up with the result [r]. Recall that the
    [Result T] type always includes the final world state, and includes a return
    value of type [T] if the execution finishes successfully without crashing.
  *)

Variable protocol : forall (tid : nat), State -> State -> Prop.


Definition rely (tid : nat) (s0 s1 : State) : Prop :=
  exists tid' T (op' : opT T) r',
  tid' <> tid /\
  protocol tid' s0 s1 /\
  op_step op' tid' s0 r' s1.


Inductive exec : forall T, proc T -> nat -> State -> Result T -> Prop :=

| ExecOther : forall T (p : proc T) T' (op: opT T') tid s s' r,
    exec p tid s' r ->
    rely tid s s' ->
    exec p tid s r

| ExecRet : forall T (v:T) tid s,
    exec (Ret v) tid s (Finished v s)

| ExecBindFinished : forall T T' (p: proc T) (p': T -> proc T') tid
                       s v s' r,
    exec p tid s (Finished v s') ->
    exec (p' v) tid s' r ->
    exec (Bind p p') tid s r

| ExecBindMismatch : forall T T' (p: proc T) (p': T -> proc T') tid
                       s,
    exec p tid s ProtocolMismatch ->
    exec (Bind p p') tid s ProtocolMismatch

| ExecOp : forall T (op: opT T) tid s v s',
    op_step op tid s v s' ->
    protocol tid s s' ->
    exec (Op op) tid s (Finished v s')

| ExecOpMismatch : forall T (op: opT T) tid s v s',
    op_step op tid s v s' ->
    ~ protocol tid s s' ->
    exec (Op op) tid s ProtocolMismatch.



Inductive exec2 : forall T, proc T -> nat -> State ->
                  Result T -> Prop :=

| Exec2Ret : forall T (v:T) w w' tid,
    clos_refl_trans _ (rely tid) w w' ->
    exec2 (Ret v) tid w (Finished v w')

| Exec2BindFinished : forall T T' (p: proc T) (p': T -> proc T') tid
                       w v w' r,
    exec2 p tid w (Finished v w') ->
    exec2 (p' v) tid w' r ->
    exec2 (Bind p p') tid w r

| Exec2BindFailed : forall T T' (p: proc T) (p': T -> proc T') tid
                       w,
    exec2 p tid w ProtocolMismatch ->
    exec2 (Bind p p') tid w ProtocolMismatch

| Exec2Op : forall T (op: opT T) tid w w'' v w',
    clos_refl_trans _ (rely tid) w w'' ->
    op_step op tid w'' v w' ->
    protocol tid w'' w' ->
    exec2 (Op op) tid w (Finished v w')

| Exec2OpFail : forall T (op: opT T) tid w w'' v w',
    clos_refl_trans _ (rely tid) w w'' ->
    op_step op tid w'' v w' ->
    ~ protocol tid w'' w' ->
    exec2 (Op op) tid w ProtocolMismatch.

Lemma exec2_allows_rely : forall w w' T (p : proc T) r tid,
  clos_refl_trans _ (rely tid) w w' ->
  exec2 p tid w' r ->
  exec2 p tid w r.
Proof.
  intros.
  generalize dependent w.
  induction H0; intros.
  - constructor. eapply rt_trans; eauto.
  - eapply Exec2BindFinished.
    + eapply IHexec2_1; eauto.
    + eapply IHexec2_2; eauto.
      eapply rt_refl.
  - eapply Exec2BindFailed. eauto.
  - eapply Exec2Op.
    2: eauto.
    2: eauto.
    eapply rt_trans; eauto.
  - eapply Exec2OpFail.
    2: eauto.
    2: eauto.
    eapply rt_trans; eauto.
Qed.

Theorem exec_exec2_equiv : forall T p tid w res,
  @exec T p tid w res <->
  @exec2 T p tid w res.
Proof.
  split; intros.
  - induction H.
    + eapply exec2_allows_rely; eauto.
      constructor; eauto.
    + constructor. apply rt_refl.
    + eapply Exec2BindFinished.
      * eapply IHexec1.
      * eapply IHexec2.
    + eapply Exec2BindFailed. eauto.
    + eapply Exec2Op. 2: eauto. 2: eauto. apply rt_refl.
    + eapply Exec2OpFail. 2: eauto. 2: eauto. apply rt_refl.
  - induction H.
    + apply Operators_Properties.clos_rt_rt1n in H.
      induction H.
      * constructor.
      * unfold rely in *. repeat deex.
        eapply ExecOther; eauto.
        unfold rely. do 4 eexists. eauto.
    + eapply ExecBindFinished; eauto.
    + eapply ExecBindMismatch; eauto.
    + apply Operators_Properties.clos_rt_rt1n in H.
      induction H.
      * constructor; eauto.
      * unfold rely in *. repeat deex.
        eapply ExecOther; eauto.
        unfold rely. do 4 eexists. eauto.
    + apply Operators_Properties.clos_rt_rt1n in H.
      induction H.
      * eapply ExecOpMismatch; eauto.
      * unfold rely in *. repeat deex.
        eapply ExecOther; eauto.
        unfold rely. do 4 eexists. eauto.
Qed.


End Proc.


Arguments ProtocolMismatch {State T}.


(** * Notation for composing procedures.

    To help us write procedures in our [proc] language, we define the
    following Haskell-like notation for [Bind].  This allows us to say:

      [[
      x <- firstProcedure;
      secondProcedure (x+1)
      ]]

    to assign the result of [firstProcedure] to [x], and then use [x]
    in an argument to [secondProcedure].  We can even use [x] inside of
    a Gallina expression before passing it to [secondProcedure], such as
    adding 1 in the example above.

    This notation does not permit silently discarding the return value of the
    first procedure. In order to run two procedures where the first one returns
    nothing (e.g., [unit]), or we want to otherwise ignore the result of the
    first procedure, we have to explicitly discard the return value by writing:

      [[
      _ <- firstProcedure;
      secondProcedure
      ]]
  *)

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

Arguments Ret {opT T} v.
