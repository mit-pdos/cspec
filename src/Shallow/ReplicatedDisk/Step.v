Require Import Automation.

Require Import Shallow.ProgLang.Hoare.

Lemma exists_tuple2 : forall A B (P: A * B -> Prop),
    (exists a b, P (a, b)) ->
    (exists p, P p).
Proof.
  intros.
  repeat deex; eauto.
Qed.

(* we use a focused hint database for rewriting because autorewrite becomes
       very slow with just a handful of patterns *)
Create HintDb rd.

Ltac simplify :=
  repeat match goal with
         | |- forall _, _ => intros
         | _ => deex
         | _ => destruct_tuple
         | |- _ /\ _ => split; [ solve [auto] | ]
         | |- _ /\ _ => split; [ | solve [auto] ]
         (* TODO: extract the match pattern inside the exists on a0 and use
                those names in exists_tuple *)
         | |- exists (_: _*_), _ => apply exists_tuple2
         | _ => progress simpl in *
         | _ => progress safe_intuition
         | _ => progress subst
         | _ => progress autorewrite with rd in *
         | [ u: unit |- _ ] => destruct u
         | [ crashinv: _ -> Prop |- _ ] =>
           match goal with
           | [ H: forall _, _ -> crashinv _ |-
                       crashinv _ ] =>
             eapply H
           end
         end.

Ltac finish :=
  repeat match goal with
         | _ => solve_false
         | _ => congruence
         | _ => solve [ intuition eauto ]
         end.

Ltac step :=
  step_prog; simplify; finish.
