Require Import Relations.Relation_Operators.
Require Import RelationClasses.

Require Import Helpers.Helpers.
Require Import Proc.


(** * Automation for inverting execution behavior. *)

Ltac inv_exec' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Theorem exec_ret : forall T (v:T) w r,
    exec (Ret v) w r ->
    match r with
    | Finished v' w' => v = v' /\ w = w'
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


Local Hint Constructors exec.

(** These are the monad laws

TODO: explain what the monad is and what these monad laws mean (specifically,
we're proving that exec treats procedures up to the monad laws as equivalences
between procedures).
 *)

Definition exec_equiv T (p: proc T) p' :=
  forall w r, exec p w r <-> exec p' w r.

Instance exec_equiv_equiv T : Equivalence (exec_equiv (T:=T)).
Proof.
  constructor; hnf; unfold exec_equiv; intros;
    repeat match goal with
           | [ H: forall (w:world) (r: Result T), _,
                 w: world,
                 r: Result T |- _ ] =>
             specialize (H w r)
           end; intuition.
Qed.

Theorem monad_left_id : forall T T' (p: T' -> proc T) v,
    exec_equiv (Bind (Ret v) p) (p v).
Proof.
  unfold exec_equiv; split; intros.
  - inv_exec; eauto.
  - eapply ExecBindFinished; eauto.
Qed.

Theorem monad_assoc : forall `(p1: proc T)
                        `(p2: T -> proc T')
                        `(p3: T' -> proc T''),
    exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  unfold exec_equiv; split; intros.
  - destruct r; repeat (inv_exec; eauto).
  - destruct r; repeat (inv_exec; eauto).
Qed.


Arguments clos_refl_trans_1n {A} R _ _.
