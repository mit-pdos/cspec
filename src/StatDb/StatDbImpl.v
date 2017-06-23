Require Import Automation.
Require Import EquivDec.
Require Import List.
Require Import Omega.

Require Import StatDb.StatDbAPI.
Require Import Variables.VariablesAPI.
Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import Refinement.ProgLang.NoCrashes.

Module StatDB.

  Section Implementation.

    Variable (vars : Interface Vars.API).

    Definition add (v : nat) : prog unit :=
      sum <- Prim vars (Vars.Read Vars.VarSum);
      count <- Prim vars (Vars.Read Vars.VarCount);
      _ <- Prim vars (Vars.Write Vars.VarSum (sum + v));
      _ <- Prim vars (Vars.Write Vars.VarCount (count + 1));
      Ret tt.

    Definition mean : prog (option nat) :=
      count <- Prim vars (Vars.Read Vars.VarCount);
      if count == 0 then
        Ret None
      else
        sum <- Prim vars (Vars.Read Vars.VarSum);
        Ret (Some (Nat.div sum count)).

    Definition init : prog InitResult :=
      _ <- Prim vars (Vars.Write Vars.VarCount 0);
      _ <- Prim vars (Vars.Write Vars.VarSum 0);
      Ret Initialized.

    Definition statdb_op_impl T (op: StatDB.Op T) : prog T :=
      match op with
      | StatDB.Add v => add v
      | StatDB.Mean => mean
      end.

    Definition impl : InterfaceImpl StatDB.Op :=
      {| op_impl := statdb_op_impl;
         recover_impl := Ret tt;
         init_impl := then_init (iInit vars) init; |}.

    Definition statdb_abstraction (vars_state : Vars.State) (statdb_state : StatDB.State) :=
      vars_state Vars.VarCount = Some (length statdb_state) /\
      vars_state Vars.VarSum = Some (fold_right plus 0 statdb_state).

    Definition abstr : Abstraction StatDB.State :=
      abstraction_compose
        (interface_abs vars)
        {| abstraction := statdb_abstraction |}.

    Definition statdb : Interface StatDB.API.
      unshelve econstructor.
      - exact impl.
      - exact abstr.
      - intros.
        destruct op; unfold op_spec;
          apply spec_abstraction_compose;
            unfold spec_impl, statdb_abstraction.
        + unfold prog_spec; intros.
          destruct a; simpl in *; intuition.
          inv_rexec.
          * repeat ( match goal with
            | H: exec (Prim _ _) _ _ |- _ => eapply RExec in H
            end || inv_exec ).
            eapply (impl_ok vars) in H9; eauto.
            deex.
            eapply (impl_ok vars) in H8; eauto.
            deex.
            eapply (impl_ok vars) in H10; eauto.
            deex.
            eapply (impl_ok vars) in H11; eauto.
            deex.

            simpl in *.
            unfold pre_step in *; repeat deex.
            repeat Vars.inv_bg.
            repeat Vars.inv_step.

            eexists; intuition.
            eauto.
            eexists; intuition.
            constructor.

            autorewrite with upd.
            rewrite H0 in H8. inversion H8; subst. f_equal. simpl. omega.

            autorewrite with upd.
            rewrite H4 in H10. inversion H10; subst. f_equal. simpl. omega.
          * cannot_crash.
        + unfold prog_spec; intros.
          destruct a; simpl in *; intuition.
          inv_rexec.
          * inv_exec.
            destruct (equiv_dec v0 0).
           -- repeat ( match goal with
              | H: exec (Prim _ _) _ _ |- _ => eapply RExec in H
              end || inv_ret || inv_exec ).

              eapply (impl_ok vars) in H9; eauto.
              deex.

              simpl in *.
              unfold pre_step in *; repeat deex.
              repeat Vars.inv_bg.
              repeat Vars.inv_step.

              eexists; intuition.
              eauto.

              destruct s; simpl in *; try congruence.
              eexists; intuition.
              constructor.
              simpl; eauto.
              simpl; eauto.
           -- repeat ( match goal with
              | H: exec (Prim _ _) _ _ |- _ => eapply RExec in H
              | H: rexec _ _ _ _ |- _ => eapply (impl_ok vars) in H; eauto; deex
              end || inv_ret || inv_exec ).

              simpl in *.
              unfold pre_step in *; repeat deex.
              repeat Vars.inv_bg.
              repeat Vars.inv_step.

              eexists; intuition.
              eauto.

              rewrite H0 in H7; inversion H7; subst.
              rewrite H4 in H9; inversion H9; subst.

              eexists; intuition.
              constructor; eauto.
              destruct s; simpl in *; try congruence; try omega.
              eauto.
              eauto.
          * cannot_crash.
      - cannot_crash.
      - eapply then_init_compose; eauto.
        unfold prog_spec; intros.
        destruct a; simpl in *; intuition.
        inv_rexec.
        * repeat ( match goal with
          | H: exec (Prim _ _) _ _ |- _ => eapply RExec in H
          | H: rexec _ _ _ _ |- _ => eapply (impl_ok vars) in H; eauto; deex
          end || inv_ret || inv_exec ).

          simpl in *.
          unfold pre_step in *; repeat deex.
          repeat Vars.inv_bg.
          repeat Vars.inv_step.

          eexists; intuition.
          eauto.
          eexists; intuition.

          instantiate (1 := nil).
          unfold statdb_abstraction; intuition.
          reflexivity.
        * cannot_crash.

      Unshelve.
      all: eauto.
    Defined.

  End Implementation.

End StatDB.
