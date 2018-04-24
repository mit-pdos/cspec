Inductive Learnt {P:Prop} :=
| AlreadyLearnt (H:P).

Ltac learn_fact H :=
  let P := type of H in
  let P := eval simpl in P in
  lazymatch goal with
    (* matching the type of H with the Learnt hypotheses means the
    learning fails even when the proposition is known by a different
    but unifiable type term *)
  | [ Hlearnt: @Learnt P |- _ ] =>
    fail 0 "already knew" P "through" Hlearnt
  | _ => pose proof (H:P); pose proof (@AlreadyLearnt P H)
  end.

Tactic Notation "learn" "that" constr(H) := learn_fact H.
