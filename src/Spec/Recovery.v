Require Import Helpers.Helpers.
Require Import Proc.
Require Import ProcTheorems.
Require Import Abstraction.

(** * Reasoning about crashes and recovery

  [Spec.Proc] defines the execution of a computer that can crash: after a
  crash, the computer stops executing, then reboots, and then runs recovery.
  The computer may crash during recovery.  To support reasoning about crashes,
  [proc_spec] above uses recovered condidition: each [proc_spec] must describe
  in which condition the computer may reboot through a recovered condition, and
  proofs of [proc_spec] must show that an implementation won't recover in any
  other recovered condition.

  You will also have to show that for every code state in which your
  implementation may end up in after a crash, your recovery procedure repairs
  the code state in which it crashed correctly and the repaired state
  corresponds to a correct spec state. Since [rexec] allows crashes during
  recovery, you must show that invoking recovery several times is ok.  This
  means you have to show that recovered condition of your recovery procedure
  implies its precondition and that the recovery procedure is idempotent.

 *)

Hint Constructors exec.

Theorem clos_refl_trans_1n_unit_tuple : forall `(R: unit * A -> unit * A -> Prop) x y u u',
    Relation_Operators.clos_refl_trans_1n R (u, x) (u', y) ->
    Relation_Operators.clos_refl_trans_1n
      (fun x y =>
         R (tt, x) (tt, y)) x y.
Proof.
  intros.
  destruct u, u'.
  remember (tt, x).
  remember (tt, y).
  generalize dependent x.
  generalize dependent y.
  induction H; intuition subst.
  - inversion Heqp0; subst.
    inversion Heqp; subst.
    constructor.
  - destruct y.
    destruct u.
    especialize IHclos_refl_trans_1n; safe_intuition.
    especialize IHclos_refl_trans_1n; safe_intuition.
    econstructor; eauto.
Qed.

(*
Theorem spec_abstraction_compose :
  forall `(spec: Specification A T State2)
    `(p: proc T)
    `(abs2: LayerAbstraction State1 State2)
    `(abs1: Abstraction State1),
    proc_spec
      (fun '(a, state2) state =>
         {| pre := pre (spec a state2) /\
                   abstraction abs2 state state2;
            post :=
              fun v state' =>
                exists state2',
                  post (spec a state2) v state2' /\
                  abstraction abs2 state' state2'; |}) p abs1 ->
    proc_spec spec p (abstraction_compose abs1 abs2).
Proof.
  intros.
  unfold proc_spec, abstraction_compose;
    simpl; intros; safe_intuition (repeat deex).
  eapply (H (a, state)) in H2; simpl in *; eauto.
  destruct r; intuition (repeat deex; eauto).
Qed.
*)


(** Helpers for defining step-based semantics. *)

Definition Semantics State T := State -> T -> State -> Prop.

Definition pre_step {opT State}
           (bg_step: State -> State -> Prop)
           (step: forall `(op: opT T), Semantics State T) :
  forall T (op: opT T), Semantics State T :=
  fun T (op: opT T) state v state'' =>
    exists state', bg_step state state' /\
          step op state' v state''.

Definition post_step {opT State}
           (step: forall `(op: opT T), Semantics State T)
           (bg_step: State -> State -> Prop) :
  forall T (op: opT T), Semantics State T :=
  fun T (op: opT T) state v state'' =>
    exists state', step op state v state' /\
          bg_step state' state''.

Definition op_spec `(sem: Semantics State T) : Specification unit T State :=
  fun (_:unit) state =>
    {|
      pre := True;
      post :=
        fun v state' => sem state v state';
    |}.
