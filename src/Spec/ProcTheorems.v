Require Import Relations.Relation_Operators.
Require Import RelationClasses.

Require Import Helpers.Helpers.
Require Import Proc.


(** * Automation for inverting execution behavior. *)

Ltac inv_exec' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Theorem exec_ret : forall opT State Sem T (v:T) w r,
    @exec opT State Sem _ (Ret v) w r ->
    match r with
    | Finished v' w' => v = v' /\ w = w'
    end.
Proof.
  intros.
  inv_exec' H; intuition.
Qed.

Ltac inv_ret :=
  match goal with
  | [ H: exec _ (Ret _) _ _ |- _ ] =>
    apply exec_ret in H; safe_intuition; subst
  end.

Ltac inv_exec :=
  match goal with
  | _ => inv_ret
  | [ H: exec _ (Bind _ _) _ _ |- _ ] =>
    inv_exec' H; repeat inv_ret
  | [ H: exec _ _ _ _ |- _ ] =>
    inv_exec' H; repeat inv_ret
  end.


Local Hint Constructors exec.

(** These are the monad laws

TODO: explain what the monad is and what these monad laws mean (specifically,
we're proving that exec treats procedures up to the monad laws as equivalences
between procedures).
 *)

Definition exec_equiv {opT T State} Sem (p: proc opT T) p' :=
  forall w r, @exec opT State Sem _ p w r <-> @exec opT State Sem _ p' w r.

Instance exec_equiv_equiv opT State Sem T : Equivalence (@exec_equiv opT T State Sem).
Proof.
  constructor; hnf; unfold exec_equiv; intros;
    repeat match goal with
           | [ H: forall (w:State) (r: Result State T), _,
                 w: State,
                 r: Result State T |- _ ] =>
             specialize (H w r)
           end; intuition.
Qed.

Theorem monad_left_id : forall opT T T' State Sem (p: T' -> proc opT T) v,
    @exec_equiv _ _ State Sem (Bind (Ret v) p) (p v).
Proof.
  unfold exec_equiv; split; intros.
  - inv_exec; eauto.
  - eapply ExecBindFinished; eauto.
Qed.

Theorem monad_assoc : forall opT State Sem
                        `(p1: proc opT T)
                        `(p2: T -> proc opT T')
                        `(p3: T' -> proc opT T''),
    @exec_equiv _ _ State Sem (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
  unfold exec_equiv; split; intros.
  - destruct r; repeat (inv_exec; eauto).
  - destruct r; repeat (inv_exec; eauto).
Qed.


Arguments clos_refl_trans_1n {A} R _ _.
