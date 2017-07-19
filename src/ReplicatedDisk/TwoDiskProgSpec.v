Require Import POCS.
Require Import TwoDisk.TwoDiskAPI.

(** Hoare-style specifications for the TwoDisk primitives.

These specifications are written in a stylized manner using the notation from
MaybeHolds. The preconditions relate both disks to the provided ghost state, and
then the postconditions are expressed entirely in terms of ghost state. This
style of specification automates well, easily carrying forward information in
proofs across several operations.

These proofs should completely specify the behavior of the TwoDisk operations,
in that any step the primitives could do can be expressed using these
specifications. The proofs of course guarantee that the primitives follow the
specifications here, but there is a possibility that the specifications are more
restrictive. While we have tried to avoid doing so, we do not prove completeness
below.
 *)

(* help out type inference *)
Implicit Type (state:TD.State).

Theorem maybe_holds_stable : forall state state' F0 F1,
    TD.disk0 state ?|= F0 ->
    TD.disk1 state ?|= F1 ->
    TD.bg_failure state state' ->
    TD.disk0 state' ?|= F0 /\
    TD.disk1 state' ?|= F1.
Proof.
  intros.
  TD.inv_bg; simpl in *; eauto.
Qed.

Ltac cleanup :=
  repeat match goal with
         | [ |- forall _, _ ] => intros
         | |- _ /\ _ => split; [ solve [ eauto || congruence ] | ]
         | |- _ /\ _ => split; [ | solve [ eauto || congruence ] ]
         | [ H: Working _ = Working _ |- _ ] => inversion H; subst; clear H
         | [ H: TD.bg_failure _ _ |- _ ] =>
           eapply maybe_holds_stable in H;
           [ | solve [ eauto ] | solve [ eauto ] ]; destruct_ands
         | [ H: _ ?|= eq _, H': _ = Some _ |- _ ] =>
                  pose proof (holds_some_inv_eq _ H' H); clear H
         | _ => deex
         | _ => destruct_tuple
         | _ => progress unfold pre_step in *
         | _ => progress unfold TD.wipe in *
         | _ => progress simpl in *
         | _ => progress subst
         | _ => progress safe_intuition
         | _ => solve [ eauto ]
         | _ => congruence
         end.

Ltac prim :=
  intros; eapply prim_spec; cleanup;
  try TD.inv_step;
  try solve [ destruct matches in *; cleanup ].

Hint Resolve holds_in_some_eq.
Hint Resolve holds_in_none_eq.
Hint Resolve pred_missing.

Theorem TDRead0_ok : forall (i: Interface TD.API) a,
    prog_spec
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state ?|= eq d_0 /\
                  TD.disk1 state ?|= F;
           post :=
             fun r state' =>
               match r with
               | Working v => TD.disk0 state' ?|= eq d_0 /\
                             TD.disk1 state' ?|= F /\
                             d_0 a ?|= eq v
               | Failed => TD.disk0 state' ?|= missing /\
                          TD.disk1 state' ?|= F
               end;
           recover :=
             fun _ state' => TD.disk0 state' ?|= eq d_0 /\
                      TD.disk1 state' ?|= F;
         |})
      (Prim i (TD.Read d0 a))
      (irec i)
      (interface_abs i).
Proof.
  prim.
Qed.

Theorem TDRead1_ok : forall (i: Interface TD.API) a,
    prog_spec
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state ?|= F /\
                  TD.disk1 state ?|= eq d_1;
           post :=
             fun r state' =>
               match r with
               | Working v => TD.disk0 state' ?|= F /\
                             TD.disk1 state' ?|= eq d_1 /\
                             d_1 a ?|= eq v
               | Failed => TD.disk0 state' ?|= F /\
                          TD.disk1 state' ?|= missing
               end;
           recover :=
             fun _ state' => TD.disk0 state' ?|= F /\
                      TD.disk1 state' ?|= eq d_1;
         |})
      (Prim i (TD.Read d1 a))
      (irec i)
      (interface_abs i).
Proof.
  prim.
Qed.

Theorem TDWrite0_ok : forall (i: Interface TD.API) a b,
    prog_spec
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state ?|= eq d_0 /\
                  TD.disk1 state ?|= F;
           post :=
             fun r state' =>
               match r with
               | Working _ => TD.disk0 state' ?|= eq (diskUpd d_0 a b) /\
                              TD.disk1 state' ?|= F
               | Failed => TD.disk0 state' ?|= missing /\
                           TD.disk1 state' ?|= F
               end;
           recover :=
             fun _ state' =>
               (TD.disk0 state' ?|= eq d_0 \/
                a < size d_0 /\ TD.disk0 state' ?|= eq (diskUpd d_0 a b)) /\
               TD.disk1 state' ?|= F;
         |})
      (Prim i (TD.Write d0 a b))
      (irec i)
      (interface_abs i).
Proof.
  prim.

  destruct matches in *; cleanup.
  destruct (lt_dec a (size d_0));
    autorewrite with upd in *;
    eauto.
Qed.

Theorem TDWrite1_ok : forall (i: Interface TD.API) a b,
    prog_spec
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state ?|= F /\
                  TD.disk1 state ?|= eq d_1;
           post :=
             fun r state' =>
               match r with
               | Working _ => TD.disk0 state' ?|= F /\
                             TD.disk1 state' ?|= eq (diskUpd d_1 a b)
               | Failed => TD.disk0 state' ?|= F /\
                          TD.disk1 state' ?|= missing
               end;
           recover :=
             fun _ state' =>
               TD.disk0 state' ?|= F /\
               (TD.disk1 state' ?|= eq d_1 \/
                a < size d_1 /\ TD.disk1 state' ?|= eq (diskUpd d_1 a b));
         |})
      (Prim i (TD.Write d1 a b))
      (irec i)
      (interface_abs i).
Proof.
  prim.

  destruct matches in *; cleanup.
  destruct (lt_dec a (size d_1));
    autorewrite with upd in *;
    eauto.
Qed.

Theorem TDDiskSize0_ok : forall (i: Interface TD.API),
    prog_spec
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state ?|= eq d_0 /\
                  TD.disk1 state ?|= F;
           post :=
             fun r state' =>
               match r with
               | Working n => n = size d_0 /\
                             TD.disk0 state' ?|= eq d_0 /\
                             TD.disk1 state' ?|= F
               | Failed => TD.disk0 state' ?|= missing /\
                          TD.disk1 state' ?|= F
               end;
           recover :=
             fun _ state' =>
               TD.disk0 state' ?|= eq d_0 /\
               TD.disk1 state' ?|= F;
         |})
      (Prim i (TD.DiskSize d0))
      (irec i)
      (interface_abs i).
Proof.
  prim.
Qed.

Theorem TDDiskSize1_ok : forall (i: Interface TD.API),
    prog_spec
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state ?|= F /\
                  TD.disk1 state ?|= eq d_1;
           post :=
             fun r state' =>
               match r with
               | Working n => n = size d_1 /\
                             TD.disk0 state' ?|= F /\
                             TD.disk1 state' ?|= eq d_1
               | Failed => TD.disk0 state' ?|= F /\
                          TD.disk1 state' ?|= missing
               end;
           recover :=
             fun _ state' =>
               TD.disk0 state' ?|= F /\
               TD.disk1 state' ?|= eq d_1;
         |})
      (Prim i (TD.DiskSize d1))
      (irec i)
      (interface_abs i).
Proof.
  prim.
Qed.

Hint Resolve
     TDRead0_ok
     TDRead1_ok
     TDWrite0_ok
     TDWrite1_ok
     TDDiskSize0_ok
     TDDiskSize1_ok.
