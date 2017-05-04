Require Import Prog.
Require Import Disk.
Require Import Automation.

Inductive diskId := d0 | d1.

Inductive DiskResult T :=
| Working (v:T)
| Failed.

Arguments Failed {T}.

Module TD.

  Inductive Op : Type -> Type :=
  | Read (i:diskId) (a:addr) : Op (DiskResult block)
  | Write (i:diskId) (a:addr) (b:block) : Op (DiskResult unit).

  Definition prog := Prog.prog Op.

  (** The state the program manipulates as it executes. *)
  Record State :=
    Disks { disk0 : option disk;
            disk1 : option disk;
            some_disk_works : disk0 = None -> disk1 = None -> False }.

  Arguments Disks disk0 disk1 some_disk_works : clear implicits.

  (** Get a particular disk from a state by id. *)
  Definition get_disk (i:diskId) (state:State) : option disk :=
    match i with
    | d0 => disk0 state
    | d1 => disk1 state
    end.

  Local Lemma d0_is_some (d_0: disk) (d_1: option disk) :
    Some d_0 = None -> d_1 = None -> False.
  Proof.
    congruence.
  Qed.

  Local Lemma d1_is_some (d_0: option disk) (d_1: disk) :
    d_0 = None -> Some d_1 = None -> False.
  Proof.
    congruence.
  Qed.

  Local Notation proof := (ltac:(first [ apply d0_is_some | apply d1_is_some ])) (only parsing).

  Definition set_disk (i:diskId) (state:State) (d:disk) : State :=
    match i with
    | d0 => Disks (Some d) (TD.disk1 state) proof
    | d1 => Disks (TD.disk0 state) (Some d) proof
    end.

  Inductive bg_step : State -> State -> Prop :=
  | step_id : forall state, bg_step state state
  | step_fail0 : forall d_0 d_1 pf,
      bg_step (Disks (Some d_0) (Some d_1) pf)
              (Disks None (Some d_1) proof)
  | step_fail1 : forall d_0 d_1 pf,
      bg_step (Disks (Some d_0) (Some d_1) pf)
              (Disks (Some d_0) None proof).

  Inductive op_step : Semantics Op State :=
  | step_read : forall a i r state,
      match get_disk i state with
      | Some d => match d a with
                 | Some b0 => r = Working b0
                 | None => False
                 end
      | None => r = Failed
      end ->
      op_step (Read i a) state r state
  | step_write : forall a i b state r state',
      match get_disk i state with
      | Some d => match d a with
                 | Some b0 => state' = set_disk i state (diskUpd d a b) /\
                             r = Working tt
                 | None => False
                 end
      | None => r = Failed /\ state' = state
      end ->
      op_step (Write i a b) state r state'.

  Definition step := background_step bg_step op_step.

  Definition exec := Prog.exec step.
  Definition exec_recover := Prog.exec_recover step.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      safe_intuition;
      match goal with
      | [ H: op_step _ _ _ _ |- _ ] =>
        inversion H; subst; clear H;
        repeat sigT_eq;
        safe_intuition
      end
    end.

  Ltac inv_bg :=
    match goal with
    | [ H: TD.bg_step _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

End TD.
