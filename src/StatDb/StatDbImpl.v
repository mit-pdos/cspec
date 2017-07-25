Require Import POCS.
Require Import StatDb.StatDbAPI.
Require Import Variables.VariablesAPI.

Import Vars.
Import StatDB.

Module StatDB.

  Section Implementation.

    Variable (vars : Interface Vars.API).

    Definition add (v : nat) : prog unit :=
      sum <- Prim vars (Read VarSum);
      count <- Prim vars (Read VarCount);
      _ <- Prim vars (Write VarSum (sum + v));
      _ <- Prim vars (Write VarCount (count + 1));
      Ret tt.

    Definition mean : prog (option nat) :=
      (* Your solutions here *)
      (* SOL *)
      count <- Prim vars (Read VarCount);
      if count == 0 then
        Ret None
      else
        sum <- Prim vars (Read VarSum);
        Ret (Some (sum / count)).

    Definition mean_stub : prog (option nat) :=
      (* END *)
      Ret (Some 0).

    Definition init : prog InitResult :=
      _ <- Prim vars (Write VarCount 0);
      _ <- Prim vars (Write VarSum 0);
      Ret Initialized.

    Definition statdb_op_impl T (op: StatDB.Op T) : prog T :=
      match op with
      | Add v => add v
      | Mean => mean
      end.

    Definition impl : InterfaceImpl StatDB.Op :=
      {| op_impl := statdb_op_impl;
         recover_impl := Ret tt;
         init_impl := then_init (iInit vars) init; |}.

    Definition statdb_abstraction (vars_state : Vars.State) (statdb_state : StatDB.State) : Prop :=
      StateCount vars_state = length statdb_state /\
      StateSum vars_state = fold_right plus 0 statdb_state.

    Definition abstr : Abstraction StatDB.State :=
      abstraction_compose
        (interface_abs vars)
        {| abstraction := statdb_abstraction |}.

    Definition statdb : Interface StatDB.API.
      unshelve econstructor.
      - exact impl.
      - exact abstr.
      - destruct op.

        + lift_world.
          prog_spec_symbolic_execute inv_bg inv_step.
          solve_final_state.

          unfold statdb_abstraction in *.
          simpl in *.
          intuition.

        + (* Prove that your implementation of [mean] refines StatDbAPI.man *)
          (* SOL *)
          lift_world.
          prog_spec_symbolic_execute inv_bg inv_step.
          * solve_final_state.

            unfold statdb_abstraction in *; intuition.
            destruct s; simpl in *; try congruence.

          * solve_final_state.

            unfold statdb_abstraction in *; intuition.
            unfold statdb_abstraction in *; intuition.
          (* END *)
          (* STUB: pocs_admit. *)

      - cannot_crash.
      - eapply then_init_compose; eauto.
        prog_spec_symbolic_execute inv_bg inv_step.

        solve_final_state.

        instantiate (1 := nil).
        simpl; auto.
        simpl; auto.
        reflexivity.

      Unshelve.
      all: eauto.
    Defined.

  End Implementation.

End StatDB.

Print Assumptions StatDB.statdb.
