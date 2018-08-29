Require Import Helpers.ProofAutomation.

Global Set Implicit Arguments.

Section Proc.

  Context {Op:Type}.

  Inductive proc :=
  | Ret
  | Exec (a:Action) (p:proc)
  with Action :=
       | Call (op:Op)
       | Spawn (p:proc)
       | Atomic (p:proc)
  .

  Fixpoint seq (p1 p2: proc) : proc :=
    match p1 with
    | Ret => p2
    | Exec a p' => Exec a (seq p' p2)
    end.

  Infix ";;" := seq (at level 14).

  Theorem seq_assoc : forall p1 p2 p3,
      p1;; p2;; p3 = p1;; (p2;; p3).
  Proof.
    induct p1; simpl; congruence.
  Qed.

  Definition seq_ret_l p :
      Ret;; p = p := eq_refl.

  Theorem seq_ret_r : forall p,
      p;; Ret = p.
  Proof.
    induct p; simpl; congruence.
  Qed.

End Proc.

Arguments proc Op : clear implicits.

Notation "p1 ;; p2" := (seq p1 p2) (at level 14, left associativity,
                                    format "p1 ;;  '/' p2").

Notation "a ~ p" := (Exec a p) (at level 13, right associativity).

(* printing test *)
Local Definition example Op (o:Op) : proc Op :=
  Call o ~ Call o ~ Ret;;
                     Spawn (Call o ~ Ret) ~ Ret.
