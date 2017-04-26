(* model of an IO monad *)

Global Set Implicit Arguments.

Axiom IO : Type -> Type.
Axiom Ret : forall T, T -> IO T.
Axiom Bind : forall T T', IO T -> (T -> IO T') -> IO T'.

(* state the IO monad manipulates *)
Axiom world : Type.

Arguments IO T.
Arguments Ret {T} v.
Arguments Bind {T T'} io io'.

Axiom io_step : forall T, IO T -> world -> T -> world -> Prop.

Axiom ret_step : forall T (v:T) w v' w',
    io_step (Ret v) w v' w' <->
    v' = v /\ w' = w.

Axiom bind_step : forall T T' (p: IO T) (p': T -> IO T') w v' w'',
    io_step (Bind p p') w v' w'' <->
    (exists v w', io_step p w v w' /\
             io_step (p' v) w' v' w'').

(* TODO: assume monad laws *)
