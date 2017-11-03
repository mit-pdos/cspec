Require Import POCS.
Require Import VariablesAPI.
Require Import StatDbAPI.

(** * An implementation of StatDB

   StatDB is built on top of the Variables API, which maintains two variables
   [VarCount] and [VarSum]. StatDB reads and writes these two variables using
   the API provided in the VarsAPI module. [VarCount] stores the number of
   integers that [VarSum] sums up. The mean is just [VarSum]/[VarCount].

  *)


  Import ListNotations.

  Definition add (v : nat) : proc VariablesAPI.opT unit :=
    sum <- Op _ _ (Read VarSum);
    count <- Op _ _ (Read VarCount);
    _ <- Op _ _ (Write VarSum (sum + v));
    _ <- Op _ _ (Write VarCount (count + 1));
    Ret tt.

  (** ** Exercise : complete the implementation of mean *)
  Definition mean : proc VariablesAPI.opT (option nat) :=
  (* SOL *)
    count <- Op _ _ (Read VarCount);
    if count == 0 then
      Ret None
    else
      sum <- Op _ _ (Read VarSum);
      Ret (Some (sum / count)).
  (* END *)
  (* STUB:   Ret None. *)

(*
  Definition init' : proc InitResult :=
    _ <- v.write VarCount 0;
    _ <- v.write VarSum 0;
    Ret Initialized.

  Definition init := then_init v.init init'.
*)

  (** ** Exercise : complete the implementation of the abstraction function: *)
  Definition statdb_abstraction (vars_state : VariablesAPI.State) (statdb_state : StatDbAPI.State) : Prop :=
  (* SOL *)
    StateCount vars_state = length statdb_state /\
    StateSum vars_state = fold_right plus 0 statdb_state.
  (* END *)
  (* STUB:   True. *)

  Definition abs : LayerAbstraction VariablesAPI.State StatDbAPI.State :=
    {| abstraction := statdb_abstraction; |}.

  Example abstr_1_ok : statdb_abstraction (VariablesAPI.mkState 0 0) nil.
  Proof. unfold statdb_abstraction; auto. Qed.

  (** ** Exercise : complete the proof for the following admitted examples *)
  Example abstr_2_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0) nil.
  Proof.
    unfold statdb_abstraction; simpl.
  (* SOL *)
    omega.
  Qed.
  (* END *)
  (* STUB: Admitted. *)

  Example abstr_3_ok : statdb_abstraction (VariablesAPI.mkState 2 3) [1; 2].
  Proof.
    unfold statdb_abstraction; simpl.
  (* SOL *)
    omega.
  Qed.
  (* END *)
  (* STUB: Admitted. *)

(*
  Theorem init_ok : init_abstraction init abstr inited.
  Proof.
    eapply then_init_compose; eauto.
    unfold init'.

    step_proc_basic; intros.
    exists tt.
    simpl; intuition idtac.

    step_proc_basic; intros.
    exists tt.
    simpl; intuition idtac.

    step_proc_basic; intros.
    eauto.

    simpl in *; intuition subst.
    exists nil.
    unfold statdb_abstraction, inited.
    intuition auto.
  Qed.
*)


  Theorem op_ok : forall opT T State (op : opT T) op_step,
    proc_spec (fun (_ : unit) (state : State) =>
      {|
        pre := True;
        post := fun (r : T) state' => op_step T op state r state';
      |}) (Op opT T op) op_step.
  Proof.
    unfold proc_spec; intros.
    inversion H0; subst; repeat sigT_eq.
    simpl in *; eauto.
  Qed.

  Hint Resolve op_ok.


  (** ** Exercise : complete the proof of [add] *)
  Theorem add_ok : forall v, proc_spec (spec_lower (add_spec v) abs) (add v) VariablesAPI.op_step.
  Proof.
    unfold add.
    intros.

    step_proc_basic; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.

    step_proc_basic; intros.
    exists tt; simpl; intuition idtac.

    step_proc_basic; intros.
    exists tt; simpl; intuition idtac.

    step_proc_basic; intros.
    exists tt; simpl; intuition idtac.

    step_proc_basic; intros.
    eauto.

    simpl in *; intuition subst.

    eexists; intuition auto.
    unfold statdb_abstraction in *; simpl in *.

    inversion H0; clear H0.
    inversion H1; clear H1.
    inversion H2; clear H2.
    inversion H3; clear H3.

    subst; repeat sigT_eq.
    simpl in *.
    deex. simpl in *.

    intuition omega.
  Qed.
  (* END *)
  (* STUB: Admitted. *)

  (** ** Exercise : complete the proof of [mean] *)
  Theorem mean_ok : proc_spec (spec_lower mean_spec abs) mean VariablesAPI.op_step.
  Proof.
    unfold mean.
    intros.

  (* SOL *)
    step_proc_basic; intros.
    destruct a'; simpl in *; intuition idtac.
    exists tt; simpl; intuition idtac.

    destruct (r == 0).

    - step_proc_basic; intros.
      eauto.

      simpl in *; intuition subst.

      unfold statdb_abstraction in *.
      deex.
      inversion H0; clear H0. simpl in *.
      subst; repeat sigT_eq. intuition subst.
      eexists.

      intuition idtac. eauto. eauto.
      destruct state1; intuition; simpl in *; try congruence.

    - step_proc_basic; intros.
      exists tt; simpl; intuition idtac.

      step_proc_basic; intros.
      eauto.

      simpl in *; intuition subst.

      unfold statdb_abstraction in *.

      inversion H0; clear H0.
      inversion H1; clear H1.
      subst; repeat sigT_eq. simpl in *. intuition subst.
      deex.

      destruct state; intuition.
      simpl in *.

      eexists; intuition auto. eauto. eauto.
      right.
      intuition ( try congruence ).
      subst. simpl in *. eauto.
  Qed.
  (* END *)
  (* STUB: Admitted. *)


