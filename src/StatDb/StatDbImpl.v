Require Import POCS.
Require Import Variables.VariablesAPI.

Import Vars.

Module StatDB.

  Definition add (v : nat) : prog unit :=
    sum <- read VarSum;
    count <- read VarCount;
    _ <- write VarSum (sum + v);
    _ <- write VarCount (count + 1);
    Ret tt.

  Definition mean : prog (option nat) :=
    count <- read VarCount;
    if count == 0 then
      Ret None
    else
      sum <- read VarSum;
      Ret (Some (sum / count)).

  Definition init : prog InitResult :=
    _ <- write VarCount 0;
    _ <- write VarSum 0;
    Ret Initialized.

  Definition statdb_recover : prog unit :=
    var_recover.


  Definition State := list nat.

  Definition statdb_abstraction (vars_state : Vars.State) (statdb_state : StatDB.State) : Prop :=
    StateCount vars_state = length statdb_state /\
    StateSum vars_state = fold_right plus 0 statdb_state.

  Definition abstr : Abstraction StatDB.State :=
    abstraction_compose
      Vars.abstr
      {| abstraction := statdb_abstraction |}.


  Theorem add_ok : forall v,
    prog_spec
      (fun (_ : unit) state => {|
        pre := True;
        post := fun r state' =>
          r = tt /\ state' = v :: state;
        recover := fun _ _ => False
      |})
      (add v) statdb_recover abstr.
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

    unfold wipe in *; intuition.
  Qed.

  Theorem mean_ok :
    prog_spec
      (fun (_ : unit) state => {|
        pre := True;
        post := fun r state' =>
          state' = state /\
          (state = nil /\ r = None \/
           state <> nil /\ r = Some (fold_right plus 0 state / length state));
        recover := fun _ _ => False
      |})
      mean statdb_recover abstr.
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
      2: unfold wipe in *; intuition.

      unfold statdb_abstraction in *.
      destruct l; intuition; simpl in *; try congruence.
      exists nil; intuition auto.

    - step_prog; intros.
      eexists (_, _); simpl; intuition idtac.

      step_prog; intros.
      eauto.

      simpl in *; intuition subst.
      2: unfold wipe in *; intuition.

      unfold statdb_abstraction in *.
      destruct l; intuition.

      eexists; intuition auto.
      right.
      intuition ( try congruence ).
  Qed.

End StatDB.

Print Assumptions StatDB.add_ok.
