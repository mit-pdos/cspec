Require Import ProgLang.Prog.
Require Import Automation.

(* Language 1 is the implementation, language 2 is the spec:

 We will show that implementation executions have corresponding high-level
 executions, where the correspondence is given via an abstraction function. *)

Section Interpreter.
  Variables opT1 opT2: Type -> Type.
  Notation prog1 := (prog opT1).
  Notation prog2 := (prog opT2).

  Variable op_impl: forall T, opT2 T -> prog1 T.

  Fixpoint interpret T (p: prog2 T) : prog1 T :=
    match p with
    | Prim op => op_impl op
    | Ret v => Ret v
    | Bind p p' => Bind (interpret p) (fun v => interpret (p' v))
    end.

  Variables State1 State2: Type.
  Variable step1: Semantics opT1 State1.
  Variable step2: Semantics opT2 State2.

  Variable invariant: State1 -> Prop.
  Variable abstraction: State1 -> State2.

  Notation exec1 := (exec step1).
  Notation exec2 := (exec step2).

  Hint Constructors exec.

  Theorem interpret_exec :
    (forall T (op: opT2 T) state v state',
        invariant state ->
        exec1 (op_impl op) state (Finished v state') ->
        step2 op (abstraction state) v (abstraction state') /\ invariant state') ->
    forall T (p: prog2 T) state v state',
      invariant state ->
      exec1 (interpret p) state (Finished v state') ->
      exec2 p (abstraction state) (Finished v (abstraction state')) /\
      invariant state'.
  Proof.
    induction p; simpl; intros.
    eapply H in H1; eauto.
    intuition eauto.

    inv_exec; eauto.

    inv_exec.
    match goal with
    | [ Hexec: exec1 (interpret p) _ _ |- _ ] =>
      eapply IHp in Hexec; eauto; safe_intuition
    end.
    match goal with
    | [ Hexec: exec1 (interpret (p0 _)) _ _ |- _ ] =>
      eapply H0 in Hexec; eauto; safe_intuition
    end.
    intuition eauto.
  Qed.

End Interpreter.
