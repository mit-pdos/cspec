Require Import Automation.

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


(** The outcome of an execution, including intermediate crash points. *)
Inductive Result T :=
| Finished (v:T) (w:world)
| Crashed (w:world).
Arguments Crashed {T} w.

(* Programs may have arbitrary behavior for each primitive. *)
Axiom step : forall T, opT T -> world -> T -> world -> Prop.

(* On crash, the world state is modified to remove mutable data according to
[world_crash]. Note that this is a function; it should be a deterministic
process to replace in-memory state with default values. *)
Axiom world_crash: world -> world.

(** [exec] specifies the execution semantics of complete programs using [step]
  as the small-step semantics of the primitive operations.

   Note that crashing is entirely modeled here: operations are always atomic,
   but otherwise crashes can occur before or after any operation. *)
Inductive exec : forall T, proc T -> world -> Result T -> Prop :=
| ExecOp : forall T (op: opT T) w v w',
    step op w v w' ->
    exec (BaseOp op) w (Finished v w')
| ExecOpCrashEnd : forall T (op: opT T) w v w',
    step op w v w' ->
    exec (BaseOp op) w (Crashed w')
| ExecCrashBegin : forall T (p: proc T) w,
    exec p w (Crashed w)
| ExecRet : forall T (v:T) w,
    exec (Ret v) w (Finished v w)
| ExecRetCrash : forall T (v:T) w,
    exec (Ret v) w (Crashed w)
| ExecBindFinished : forall T T' (p: proc T) (p': T -> proc T')
                       w v w' r,
    exec p w (Finished v w') ->
    exec (p' v) w' r ->
    exec (Bind p p') w r
| ExecBindCrashed : forall T T' (p: proc T) (p': T -> proc T')
                      w w',
    exec p w (Crashed w') ->
    exec (Bind p p') w (Crashed w').

(** analogous to [Result] for recovery *)
Inductive RResult T R :=
| RFinished (v:T) (w:world)
| Recovered (v:R) (w:world).

Arguments RFinished {T R} v w.
Arguments Recovered {T R} v w.

(** Run rec in w until it finishes, restarting whenever it crashes.

   This models running rec in an infinite retry loop.
 *)
Inductive exec_recover R (rec:proc R) (w:world) : R -> world -> Prop :=
| ExecRecoverExec : forall v w',
    exec rec w (Finished v w') ->
    exec_recover rec w v w'
| ExecRecoverCrashDuringRecovery : forall w' v w'',
    exec rec w (Crashed w') ->
    exec_recover rec (world_crash w') v w'' ->
    exec_recover rec w v w''.

(** [rexec] gives semantics for running a program and using some recovery
      procedure on crashes, including crashes during recovery.

     Similar to [exec] above, behavior for recovery is specified entirely here.
     In particular, note that we (currently) recovery from exactly the crash
     w - in practice, some semantics record mutable w as some subset of
     [world]s, which should be discarded before recovery.

     Note that this is a thin wrapper that chains execution and recovery
     self-execution - the constructors are not recursive.
 *)
Inductive rexec T R : proc T -> proc R -> world -> RResult T R -> Prop :=
| RExec : forall (p:proc T) (rec:proc R) w v w',
    exec p w (Finished v w') ->
    rexec p rec w (RFinished v w')
| RExecCrash : forall (p:proc T) (rec:proc R) w w' rv w'',
    exec p w (Crashed w') ->
    exec_recover rec (world_crash w') rv w'' ->
    rexec p rec w (Recovered rv w'').

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

Arguments Ret {T} v.

(** * Automation for inverting execution behavior. *)

Ltac inv_exec' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Theorem exec_ret : forall T (v:T) w r,
    exec (Ret v) w r ->
    match r with
    | Finished v' w' => v = v' /\ w = w'
    | Crashed w' => w = w'
    end.
Proof.
  intros.
  inv_exec' H; intuition.
Qed.

Ltac inv_ret :=
  match goal with
  | [ H: exec (Ret _) _ _ |- _ ] =>
    apply exec_ret in H; safe_intuition; subst
  end.

Ltac inv_exec :=
  match goal with
  | _ => inv_ret
  | [ H: exec (Bind _ _) _ _ |- _ ] =>
    inv_exec' H; repeat inv_ret
  | [ H: exec _ _ _ |- _ ] =>
    inv_exec' H; repeat inv_ret
  end.

Ltac inv_rexec :=
  match goal with
  | [ H: rexec (Ret _) _ _ _ |- _ ] =>
    inv_exec' H
  | [ H: rexec _ _ _ _ |- _ ] =>
    inv_exec' H
  end.
