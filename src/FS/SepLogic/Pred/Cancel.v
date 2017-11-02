Require Import List.
Require Import SepLogic.Pred.Def.
Require Import SepLogic.Pred.Ptsto.
Import ListNotations.


Definition pred_fold_left `(l : list (pred A V)) : pred A V :=
  match l with
  | nil => emp
  | a :: t => fold_left star t a
  end.

Definition stars `(ps : list (pred A V)) :=
  pred_fold_left ps.
Arguments stars : simpl never.


Lemma flatten_emp : forall A V,
  (@emp A V) === stars nil.
Admitted.

Lemma flatten_default : forall `(p : pred A V),
  p === stars (p :: nil).
Admitted.

Lemma flatten_star : forall `(p : pred A V) q ps qs,
  p === stars ps
  -> q === stars qs
  -> p * q === stars (ps ++ qs).
Admitted.

Ltac flatten :=
  repeat match goal with
  | [ |- emp === _ ] => apply flatten_emp
  | [ |- _ * _ === _ ] => eapply flatten_star
  | _ => apply flatten_default
  end.

Example flatten1 : forall `(p : pred A V) q r s t u, exists l, p * q * r * (s * t) * u === stars l /\ l = nil.
Proof.
  intros. eexists. split. flatten. simpl.
Abort.


Theorem start_normalizing_left : forall `(p : pred A V) q ps,
  p === stars ps
  -> ((stars ps * stars nil) ===> q)
  -> p ===> q.
Admitted.

Theorem start_normalizing_right : forall `(p : pred A V) q qs,
  q === stars qs
  -> (p ===> stars qs)
  -> p ===> q.
Admitted.

Ltac norml := eapply start_normalizing_left; [ flatten | ]; simpl app.
Ltac normr := eapply start_normalizing_right; [ flatten | ]; simpl app.
Ltac norm := norml; normr.
Ltac denorm := unfold stars; simpl.

Example norm1 : forall `(p : pred A V) q r s,
  p * q * r * s ===> (p * q) * (s * r).
Proof.
  intros.
  norm.
Abort.


Definition okToUnify `(p1 : pred A V) p2 := p1 = p2.
Hint Extern 0 (okToUnify ?a ?a) => constructor : okToUnify.
Hint Extern 0 (okToUnify (ptsto ?p _) (ptsto ?p _)) => constructor : okToUnify.


Inductive pick {A V} (lhs : pred A V) : list (pred A V) -> list (pred A V) -> Prop :=
| PickFirst : forall p ps,
  okToUnify lhs p
  -> pick lhs (p :: ps) ps
| PickLater : forall p ps ps',
  pick lhs ps ps'
  -> pick lhs (p :: ps) (p :: ps').

Ltac pick :=
  solve [ repeat
          ( (apply PickFirst; solve [ trivial with okToUnify ]) ||
            apply PickLater ) ].


Theorem cancel_one : forall `(p : pred A V) qs qs' ps F,
  pick p qs qs'
  -> stars ps * F ===> stars qs'
  -> stars (p :: ps) * F ===> stars qs.
Admitted.

Theorem delay_one : forall `(p : pred A V) ps q qs,
  stars ps * stars (p :: qs) ===> q
  -> stars (p :: ps) * stars qs ===> q.
Admitted.

Ltac cancel_one := eapply cancel_one; [ pick | ].
Ltac delay_one := apply delay_one.


Lemma cancel_finish : forall A V ps qs,
  stars ps ===> stars qs ->
  @stars A V [] * stars ps ===> stars qs.
Admitted.

Ltac cancel_finish := apply cancel_finish.

Ltac cancel := repeat ( cancel_one || delay_one ); apply cancel_finish.



Example cancel1 : forall `(p : pred A V) q r s,
  p * q * r * s ===> (p * q) * (s * r).
Proof.
  intros.
  norm. cancel. reflexivity.
Qed.
