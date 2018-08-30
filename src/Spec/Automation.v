Require Import Helpers.Instances.

Ltac cleanup_upd :=
  autorewrite with t in *;
  repeat match goal with
         | [ H: Some _ = Some _ |- _ ] =>
           inversion H; subst; clear H
         | [ H: Some _ = None |- _ ] =>
           solve [ inversion H ]
         end;
  trivial.

Ltac cmp_ts tid tid' :=
  destruct (equal_dec tid tid');
  subst;
  cleanup_upd.
