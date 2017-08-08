Require Export FunctionalExtensionality.

Require Import Helpers.Automation.

Global Set Implicit Arguments.

(* [mem A V] is a partial function from A to V, which we interpret as a very
general type of memory with addresses of type A and values of type V. *)
Definition mem A V := A -> option V.
Definition empty_mem {A V} : @mem A V := fun _ => None.

(* This enables Coq's generalization feature: definitions will use [`(m: mem A
V)] (note the backtic); A and V, even if not bound, will be added as parameters
before [m]. By default no variables can be generalized; [Generalizable
Variables] allows to add identifers that are legal to generalize. *)
Global Generalizable Variables A V.
