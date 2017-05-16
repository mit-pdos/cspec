Require Import Automation.
Require Import MaybeHolds.
Require Import Disk.

Require Import Shallow.ProgLang.Hoare.
Require Import Shallow.ProgLang.Prog.
Require Import Shallow.TwoDiskAPI.

Require Import Shallow.Interface.

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

Ltac start_prim :=
  intros; eapply prim_ok; intros;
  repeat destruct_tuple;
  simpl in *;
  safe_intuition;
  try solve [ intuition eauto ].

Ltac cleanup :=
  repeat match goal with
         | [ |- forall _, _ ] => intros
         | _ => progress simpl in *
         | _ => progress safe_intuition
         | _ => progress subst
         | _ => destruct_tuple
         | _ => deex
         | _ => simpl_match
         | |- _ /\ _ => split; [ solve [ eauto || congruence ] | ]
         | |- _ /\ _ => split; [ | solve [ eauto || congruence ] ]
         | [ H: Working _ = Working _ |- _ ] => inversion H; subst; clear H
         | [ |- exists (_:unit), _ ] => exists tt
         | _ => solve [ eauto ]
         | _ => congruence
         end.

Hint Resolve holds_in_some.
Hint Resolve holds_in_some_eq.
Hint Resolve holds_in_none_eq.

Theorem TDRead0_ok : forall (i: Interface TD.API) a,
    prog_ok
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state |= eq d_0 /\
                  TD.disk1 state |= F;
           post :=
             fun r state' =>
               match r with
               | Working v => TD.disk0 state' |= eq d_0 /\
                             TD.disk1 state' |= F /\
                             d_0 a |= eq v
               | Failed => TD.disk0 state' |= missing /\
                          TD.disk1 state' |= F
               end;
           crash :=
             fun state' => TD.disk0 state' |= eq d_0 /\
                    TD.disk1 state' |= F;
         |})
      (get_op i (TD.Read d0 a))
      (refinement i).
Proof.
  start_prim; cleanup.
  TD.inv_step.
  TD.inv_bg; cleanup;
    repeat (destruct matches in *; cleanup).
Qed.

Theorem TDRead1_ok : forall a,
    prog_ok
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state |= F /\
                  TD.disk1 state |= eq d_1;
           post :=
             fun r state' =>
               match r with
               | Working v => TD.disk0 state' |= F /\
                             TD.disk1 state' |= eq d_1 /\
                             d_1 a |= eq v
               | Failed => TD.disk0 state' |= F /\
                          TD.disk1 state' |= missing
               end;
           crash :=
             fun state' => TD.disk0 state' |= F /\
                    TD.disk1 state' |= eq d_1;
         |})
      (Prim (TD.Read d1 a))
      TD.step.
Proof.
  start_prim.
  TD.inv_step.
  TD.inv_bg; cleanup;
    repeat (destruct matches in *; cleanup).
Qed.

Theorem TDWrite0_ok : forall a b,
    prog_ok
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state |= eq d_0 /\
                  TD.disk1 state |= F;
           post :=
             fun r state' =>
               match r with
               | Working _ => TD.disk0 state' |= eq (diskUpd d_0 a b) /\
                             TD.disk1 state' |= F
               | Failed => TD.disk0 state' |= missing /\
                          TD.disk1 state' |= F
               end;
           crash :=
             fun state' =>
               TD.disk0 state' |= eq d_0 /\
               TD.disk1 state' |= F;
         |})
      (Prim (TD.Write d0 a b))
      TD.step.
Proof.
  start_prim.
  TD.inv_step; simpl.
  TD.inv_bg; cleanup;
    repeat (destruct matches in *; cleanup).
Qed.

Theorem TDWrite1_ok : forall a b,
    prog_ok
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state |= F /\
                  TD.disk1 state |= eq d_1;
           post :=
             fun r state' =>
               match r with
               | Working _ => TD.disk0 state' |= F /\
                             TD.disk1 state' |= eq (diskUpd d_1 a b)
               | Failed => TD.disk0 state' |= F /\
                          TD.disk1 state' |= missing
               end;
           crash :=
             fun state' =>
               TD.disk0 state' |= F /\
               TD.disk1 state' |= eq d_1;
         |})
      (Prim (TD.Write d1 a b))
      TD.step.
Proof.
  start_prim.
  TD.inv_step; simpl.
  TD.inv_bg; cleanup;
    repeat (destruct matches in *; cleanup).
Qed.

Theorem TDDiskSize0_ok :
    prog_ok
      (fun '(d_0, F) state =>
         {|
           pre := TD.disk0 state |= eq d_0 /\
                  TD.disk1 state |= F;
           post :=
             fun r state' =>
               match r with
               | Working n => n = size d_0 /\
                             TD.disk0 state' |= eq d_0 /\
                             TD.disk1 state' |= F
               | Failed => TD.disk0 state' |= missing /\
                          TD.disk1 state' |= F
               end;
           crash :=
             fun state' =>
               TD.disk0 state' |= eq d_0 /\
               TD.disk1 state' |= F;
         |})
      (Prim (TD.DiskSize d0))
      TD.step.
Proof.
  start_prim.
  TD.inv_step; simpl.
  TD.inv_bg; cleanup;
    repeat (destruct matches in *; cleanup).
Qed.

Theorem TDDiskSize1_ok :
    prog_ok
      (fun '(F, d_1) state =>
         {|
           pre := TD.disk0 state |= F /\
                  TD.disk1 state |= eq d_1;
           post :=
             fun r state' =>
               match r with
               | Working n => n = size d_1 /\
                             TD.disk0 state' |= F /\
                             TD.disk1 state' |= eq d_1
               | Failed => TD.disk0 state' |= F /\
                          TD.disk1 state' |= missing
               end;
           crash :=
             fun state' =>
               TD.disk0 state' |= F /\
               TD.disk1 state' |= eq d_1;
         |})
      (Prim (TD.DiskSize d1))
      TD.step.
Proof.
  start_prim.
  TD.inv_step; simpl.
  TD.inv_bg; cleanup;
    repeat (destruct matches in *; cleanup).
Qed.

Hint Extern 1 {{ Prim (TD.Read d0 _); _}} => apply TDRead0_ok : prog.
Hint Extern 1 {{ Prim (TD.Read d1 _); _}} => apply TDRead1_ok : prog.
Hint Extern 1 {{ Prim (TD.Write d0 _ _); _}} => apply TDWrite0_ok : prog.
Hint Extern 1 {{ Prim (TD.Write d1 _ _); _}} => apply TDWrite1_ok : prog.
Hint Extern 1 {{ Prim (TD.DiskSize d0); _}} => apply TDDiskSize0_ok : prog.
Hint Extern 1 {{ Prim (TD.DiskSize d1); _}} => apply TDDiskSize1_ok : prog.
