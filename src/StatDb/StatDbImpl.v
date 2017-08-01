Require Import POCS.
Require Import Variables.VariablesAPI.
Require Import StatDb.StatDbAPI.


Module StatDB (v : VarsAPI) <: StatDbAPI.

  Definition add (v : nat) : prog unit :=
    sum <- v.read VarSum;
    count <- v.read VarCount;
    _ <- v.write VarSum (sum + v);
    _ <- v.write VarCount (count + 1);
    Ret tt.

  Definition mean : prog (option nat) :=
    count <- v.read VarCount;
    if count == 0 then
      Ret None
    else
      sum <- v.read VarSum;
      Ret (Some (sum / count)).

  Definition init' : prog InitResult :=
    _ <- v.write VarCount 0;
    _ <- v.write VarSum 0;
    Ret Initialized.

  Definition init := then_init v.init init'.

  Definition recover : prog unit :=
    v.recover.


  Definition statdb_abstraction (vars_state : VariablesAPI.State) (statdb_state : StatDbAPI.State) : Prop :=
    StateCount vars_state = length statdb_state /\
    StateSum vars_state = fold_right plus 0 statdb_state.

  Definition abstr : Abstraction StatDbAPI.State :=
    abstraction_compose
      v.abstr
      {| abstraction := statdb_abstraction |}.


  Theorem init_ok : init_invariant init recover abstr inited.
  Proof.
    eapply then_init_compose; eauto.
    unfold init'.

    step_prog; intros.
    exists (StateCount state, StateSum state); simpl; intuition idtac.

    step_prog; intros.
    exists (StateCount state0, StateSum state0); simpl; intuition idtac.

    step_prog; intros.
    eauto.

    simpl in *; intuition subst.
    exists nil.
    unfold statdb_abstraction, inited.
    intuition auto.
  Qed.

  Theorem add_ok : forall v, prog_spec (add_spec v) (add v) recover abstr.
  Proof.
    unfold add.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    eexists (_, _); simpl; intuition idtac.

    step_prog; intros.
    eexists (_, _); simpl; intuition idtac.

    step_prog; intros.
    eexists (_, _); simpl; intuition idtac.

    step_prog; intros.
    eexists (_, _); simpl; intuition idtac.

    step_prog; intros.
    eauto.

    simpl in *; intuition subst.

    eexists; intuition auto.
    unfold statdb_abstraction in *; simpl in *.
    intuition omega.

    autounfold in *; intuition.
  Qed.

  Theorem mean_ok : prog_spec mean_spec mean recover abstr.
  Proof.
    unfold mean.
    intros.

    apply spec_abstraction_compose; simpl.

    step_prog; intros.
    destruct a'; simpl in *; intuition idtac.
    eexists (_, _); simpl; intuition idtac.

    destruct (r == 0).

    - step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: autounfold in *; intuition.

      unfold statdb_abstraction in *.
      destruct s; intuition; simpl in *; try congruence.
      exists nil; intuition auto.

    - step_prog; intros.
      eexists (_, _); simpl; intuition idtac.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: autounfold in *; intuition.

      unfold statdb_abstraction in *.
      destruct s; intuition.

      eexists; intuition auto.
      right.
      intuition ( try congruence ).
  Qed.

  Theorem recover_noop : rec_noop recover abstr no_crash.
  Proof.
    unfold rec_noop.
    intros.

    apply spec_abstraction_compose; simpl.
    step_prog; intros.
    eauto.

    destruct a; simpl in *.
    intuition.
    eauto.
  Qed.

End StatDB.


Require Import VariablesImpl.
Module x := StatDB Vars.
Print Assumptions x.add_ok.
