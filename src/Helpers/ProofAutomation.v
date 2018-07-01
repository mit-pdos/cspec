(** * Proof automation.

    To help prove various theorems, we provide some basic automation.
    This automation takes the form of Ltac scripts that are designed
    to solve certain types of goals, or simplify the goal in some way.
    We also use hints (using various [Hint] statements), which is a
    way to tell Coq which theorems should be used by tactics like
    [auto], [eauto], [autorewrite], and so on.
  *)

Require Export Helpers.ProofAutomation.Abstract.
Require Export Helpers.ProofAutomation.ExistentialVariants.
Require Export Helpers.ProofAutomation.Misc.
Require Export Helpers.ProofAutomation.Propositional.
Require Export Helpers.ProofAutomation.SimplMatch.
