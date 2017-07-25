Require Export List.
Require Export Omega.

Require Export Helpers.Automation.
Require Export Helpers.Helpers.

Require Export SepLogic.Mem.Def.
Require Export SepLogic.Mem.Upd.
Require Export SepLogic.Mem.Sized.

Require Export SepLogic.Pred.Def.
Require Export SepLogic.Pred.Ptsto.
Require Export SepLogic.Pred.Impl.
Require Export SepLogic.Pred.Except.
Require Export SepLogic.Pred.MemIs.
Require Export SepLogic.Pred.MemIsExcept.

Require Export Disk.SimpleDisk.
Require Export Disk.Sectors.

Require Export Refinement.Interface.
Require Export Refinement.Prog.
Require Export Refinement.Hoare.
Require Export Refinement.NoCrashes.


(**
 * Automation for proving [prog_spec] goals in early labs by calling [inversion]
 * on [rexec] relations.
 *)

Ltac prog_spec_to_rexec :=
  unfold prog_spec;
  let x := fresh in intro x; destruct x;
  intros.

Ltac rexec_to_exec_finished :=
  inv_rexec; try cannot_crash.

Ltac case_destruct cond :=
  destruct cond eqn:?; subst; simpl in *.

Ltac symbolic_exec_one :=
  match goal with
  | H: exec ?p _ _ |- _ =>
    match p with
    | context[if ?expr then _ else _] => case_destruct expr
    | context[match ?expr with _ => _ end] => case_destruct expr
    end
  | H: exec (Prim _ _) _ _ |- _ => eapply RExec in H
  | H: exec (Ret _) _ _ |- _ => apply exec_ret in H; safe_intuition; subst
  | H: exec (Bind _ _) _ _ |- _ => inv_exec' H
  | H: exec _ _ _ |- _ => inv_exec' H
  | H: rexec _ _ _ _ |- _ => eapply impl_ok in H; [ | eassumption | solve [ simpl; eauto ] ]
  end.

Ltac symbolic_exec_many :=
  repeat symbolic_exec_one;
  simpl in *; unfold pre_step in *; repeat deex.

Ltac symbolic_exec inv_step :=
  repeat ( symbolic_exec_many || inv_step ).

Ltac match_abstraction_for_step :=
  match goal with
  | H : abstraction ?a ?w ?state |- exists _, abstraction ?a ?w _ /\ _ =>
    exists state; split; [ exact H | ]
  end;
  repeat match goal with
  | H : abstraction _ _ _ |- _ => clear H
  | w : world |- _ => clear w
  end.

Ltac step_high_level_semantics :=
  eexists; split; [ constructor | ].

Ltac lift_world :=
  apply spec_abstraction_compose.

Ltac prog_spec_symbolic_execute inv_step :=
  prog_spec_to_rexec;
  rexec_to_exec_finished;
  symbolic_exec inv_step.

Ltac solve_final_state :=
  match_abstraction_for_step;
  exact I || ( step_high_level_semantics; try assumption ).
