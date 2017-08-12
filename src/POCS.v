(** * 6.826 lab assignments common infrastructure

    This file provides common infrastructure for the lab assignments for
    6.826 (Principles of Computer Systems).  You can explore this common
    infrastructure by browsing the coqdoc documentation for the libraries
    imported here.  Click on the module name after the [Require Export]
    statement, and you should get the documentation for that module.

    All of the code you will be writing for 6.826 lab assignments will
    import all of this common infrastructure using [Require Import POCS],
    which you will see at the top of the files we will be giving you for
    the labs.
  *)

(** We include some libraries from the Coq standard library.
    [List] provides linked lists, and [Omega] provides a tactic for
    proving simple arithmetic facts.
  *)

Require Export List.
Require Export Omega.

(** XXX *)

Require Export Helpers.Helpers.
Require Export Helpers.Disk.

(** XXX *)

Require Export Refinement.Proc.
Require Export Refinement.Hoare.
