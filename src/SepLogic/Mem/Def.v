Global Set Implicit Arguments.

Definition mem A V := A -> option V.
Definition empty_mem {A V} : @mem A V := fun _ => None.
