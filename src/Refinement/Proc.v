(** * Modeling of programs and their execution. *)

Global Set Implicit Arguments.
Global Generalizable All Variables.

(** * Model of state.

    In our labs, we want to reason about programs that have side-effects,
    such as modifying the contents of memory or writing to disk.  This is
    in contrast to the kinds of programs that one can naturally write in
    Coq's Gallina language, which are purely functional; they have no
    built-in notion of mutable state.

    To reason about programs that manipulate mutable state,
    we need to construct an explicit Coq model of:

    - What the mutable state looks like.
    - What a program looks like.
    - How a program executes (and modifies the mutable state).

    Our programs will eventually be extracted from Coq into Haskell, and
    execute as Haskell programs (by compiling their Coq-generated Haskell
    source code using a Haskell compiler to produce an executable binary).

    We reflect this in our model of the world, by representing the state
    of the world with an opaque type called [world], which is defined in
    Coq as an [Axiom].
  *)

Axiom world : Type.

(** * Model of programs.

    To go along with our opaque model of the world, we similarly have an
    opaque type of programs (represented by a procedure, [proc]).  This
    represents real Haskell programs that will eventually run with the
    help of a Haskell compiler.

    To write programs in Coq, we will eventually state axioms about the
    existence of some basic procedures, implemented outside of Coq (i.e.,
    in Haskell), along with axioms about what happens when we run one of
    those basic procedures.  But that will show up later on.

    The only detail we expose about our opaque procedures is that it's
    possible to combine procedures together, using [Ret] and [Bind], as
    with monadic programs in Haskell.
  *)

(** As a technical detail, we let programs include arbitrary operations
    of types [opT T] (which will produce a T-typed result).  This represents
    the opaque execution of Haskell procedures, which Coq should not be able
    to peek inside.
  *)

Axiom opT: Type -> Type.

(** Our minimal, generic programming language.
    Programs can be combined with [Bind] and [Ret].
    [BaseOp] represents opaque Haskell code, and it's important here
    because in its absence, Coq could prove that the programming language
    never does anything other than return a constant expression with [Ret].

    Procedures are parametrized by type [T], which is the type of value
    that will be returned by the procedure.  For example, a procedure
    that returns a [nat] has type [proc nat], and a procedure that returns
    nothing ("void", in C terminology) has type [proc unit].
  *)

CoInductive proc : forall T:Type, Type :=
| BaseOp : forall T, opT T -> proc T
| Ret : forall T, T -> proc T
| Bind : forall T T', proc T -> (T -> proc T') -> proc T'.


(** Here we connect our definition of the procedure language, [proc],
    to Haskell's built-in implementations of [Bind] and [Ret], which are
    [return] and [(>>=)] respectively.  We instruct Coq to extract any
    use of [BaseOp] to an error expression, since we do not expect any
    legitimate use of [BaseOp] in Gallina.  We also instruct Coq to
    extract any attempts to pattern-match a procedure to an error, since
    we do not expect any legitimate code to pattern-match the contents of
    a [proc] procedure.
  *)

Extraction Language Haskell.

Extract Inductive proc => "TheProc"
                           ["error 'accessing BaseOp'" "return" "(>>=)"]
                           "(\fprim fret fbind -> error 'pattern match on proc')".


(** * Execution model.

    Finally, we define our model of execution.  We start by defining
    the possible outcomes of executing a procedure [proc T]: either
    the procedure finishes and returns something of type T, or the
    procedure crashes.  Because we are explicitly modeling the effect
    of procedures on the state of our system, both of these outcomes
    also include the resulting world state.
  *)

Inductive Result T :=
| Finished (v:T) (w:world)
| Crashed (w:world).

Arguments Crashed {T} w.

(** To define the execution of programs, we need to state an axiom
    about how our opaque [BaseOp] Haskell procedures will execute.
    This axiom is [step].  For every [opT T], it relates a starting
    world state to the return value of that [BaseOp] and the resulting
    world state.  This is largely just a technicality.
  *)

Axiom step : forall T, opT T -> world -> T -> world -> Prop.

(** We also need to model what happens to the state of our system on
    a crash.  Our model is that, on a crash, the world state is modified
    according to the opaque [world_crash] function, which we define as an
    axiom.  This is meant to represent the computer losing volatile state,
    such as memory contents or disk write buffers.
  *)

Axiom world_crash : world -> world.

(** Finally, we define the [exec] relation to represent the execution
    semantics of a procedure, leveraging the [step] and [world_crash]
    definitions from above.
  *)

Inductive exec : forall T, proc T -> world -> Result T -> Prop :=

(** There are three interesting aspects of this definition:

    - First, it defines how [Bind] and [Ret] work, in the [ExecRet]
      and [ExecBindFinished] constructors.
  *)

| ExecRet : forall T (v:T) w,
    exec (Ret v) w (Finished v w)
| ExecBindFinished : forall T T' (p: proc T) (p': T -> proc T')
                       w v w' r,
    exec p w (Finished v w') ->
    exec (p' v) w' r ->
    exec (Bind p p') w r

(** - Second, it defines how Haskell code runs, by referring back to
      the [step] relation that we introduced above.
  *)

| ExecOp : forall T (op: opT T) w v w',
    step op w v w' ->
    exec (BaseOp op) w (Finished v w')

(** - And finally, it defines how procedures can crash.  Any procedure
      can crash just before it starts running.  [BaseOp] procedures
      can also crash just after they finish.  And [Bind] can crash in
      the middle of running the first sub-procedure.  Crashes during the
      second sub-procedure of a [Bind] are covered by [ExecBindFinished]
      above.
  *)

| ExecCrashBegin : forall T (p: proc T) w,
    exec p w (Crashed w)
| ExecOpCrashEnd : forall T (op: opT T) w v w',
    step op w v w' ->
    exec (BaseOp op) w (Crashed w')
| ExecBindCrashed : forall T T' (p: proc T) (p': T -> proc T')
                      w w',
    exec p w (Crashed w') ->
    exec (Bind p p') w (Crashed w').


(** * Execution model with recovery.

    We also define a model of how our system executes procedures in the
    presence of recovery after a crash.  What we want to model is a system
    that, after a crash, reboots and starts running some recovery procedure
    (like [fsck] in a Unix system to fix up the state of a file system).
    If the system crashes again while running the recovery procedure, it
    starts running the same recovery procedure again after reboot.

    The outcome of running a procedure with recovery is similar to the
    [Result] type defined above, except that in the case of a crash, we
    run a recovery procedure and get both a final state _and_ a return
    value from the recovery procedure.
  *)

Inductive RResult T R :=
| RFinished (v:T) (w:world)
| Recovered (v:R) (w:world).

Arguments RFinished {T R} v w.
Arguments Recovered {T R} v w.

(** To help us talk about repeated recovery attempts (in the face of
    repeated crashes during recovery), we use [exec_recover] to model
    these repeated executions of some recovery procedure [rec].
  *)

Inductive exec_recover R (rec:proc R) (w:world) : R -> world -> Prop :=

(** The first constructor, [ExecRecoverExec], says that if the recovery
    procedure [rec] executes and finishes normally, then that's a possible
    outcome for [exec_recover].
  *)

| ExecRecoverExec : forall v w',
    exec rec w (Finished v w') ->
    exec_recover rec w v w'

(** The second constructor, [ExecRecoverCrashDuringRecovery], says that
    if [rec] started in some state [w] and crashed in state [w'], and
    we then recursively ran [rec] on every crash starting with [world_crash w']
    (by recursively referring to the [exec_recover] relation), then the
    outcome of this recursive call to [exec_recover] is an outcome for
    this constructor too.  This models repeated recovery attempts.
  *)

| ExecRecoverCrashDuringRecovery : forall w' v w'',
    exec rec w (Crashed w') ->
    exec_recover rec (world_crash w') v w'' ->
    exec_recover rec w v w''.

(** Finally, [rexec] defines what it means to run a procedure and use
    some recovery procedure on crashes, including crashes during recovery.
    [rexec] says that:

    - either the original procedure [p] finishes and returns a [RFinished]
      outcome, or
    - [p] crashes, and after running the recovery procedure [rec] one or
      more times, the system eventually stops crashing, [rec] finishes,
      and produces a [Recovered] outcome.
  *)

Inductive rexec T R : proc T -> proc R -> world -> RResult T R -> Prop :=
| RExec : forall (p:proc T) (rec:proc R) w v w',
    exec p w (Finished v w') ->
    rexec p rec w (RFinished v w')
| RExecCrash : forall (p:proc T) (rec:proc R) w w' rv w'',
    exec p w (Crashed w') ->
    exec_recover rec (world_crash w') rv w'' ->
    rexec p rec w (Recovered rv w'').

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

    This notation does not allow us to silently discard the result of a
    procedure, so in order to run two procedures where the first one returns
    nothing (e.g., [unit]), or we want to otherwise ignore the result of the
    first procedure, we have to write:

      [[
      _ <- firstProcedure;
      secondProcedure
      ]]
  *)

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

Arguments Ret {T} v.
