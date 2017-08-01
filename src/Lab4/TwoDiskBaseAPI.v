Require Import POCS.


Inductive diskId := d0 | d1.

Inductive DiskResult T :=
| Working (v:T)
| Failed.

Arguments Failed {T}.

Record State := Disks {
  disk0 : option disk;
  disk1 : option disk;
  some_disk_works : disk0 = None -> disk1 = None -> False
}.

Definition get_disk (i:diskId) (state:State) : option disk :=
  match i with
  | d0 => disk0 state
  | d1 => disk1 state
  end.

Definition set_disk (i:diskId) (state:State) (d:disk) : State :=
  match i with
  | d0 => @Disks (Some d) (disk1 state) ltac:(congruence)
  | d1 => @Disks (disk0 state) (Some d) ltac:(congruence)
  end.

Inductive Op : Type -> Type :=
| op_read (i : diskId) (a : addr) : Op (DiskResult block)
| op_write (i : diskId) (a : addr) (b : block) : Op (DiskResult unit)
| op_disksize (i : diskId) : Op (DiskResult nat).

Inductive op_step : forall `(op: Op T), Semantics State T :=
| step_read : forall a i r state,
    match get_disk i state with
    | Some d => match d a with
               | Some b0 => r = Working b0
               | None => exists b, r = Working b
               end
    | None => r = Failed
    end ->
    op_step (op_read i a) state r state
| step_write : forall a i b state r state',
    match get_disk i state with
    | Some d => state' = set_disk i state (diskUpd d a b) /\
               r = Working tt
    | None => r = Failed /\ state' = state
    end ->
    op_step (op_write i a b) state r state'
| step_size : forall i state r,
    match get_disk i state with
    | Some d => r = Working (size d)
    | None => r = Failed
    end ->
    op_step (op_disksize i) state r state.

Inductive bg_failure : State -> State -> Prop :=
| step_id : forall (state: State), bg_failure state state
| step_fail0 : forall d_0 d_1 pf,
    bg_failure (@Disks (Some d_0) (Some d_1) pf)
               (@Disks None (Some d_1) ltac:(congruence))
| step_fail1 : forall d_0 d_1 pf,
    bg_failure (@Disks (Some d_0) (Some d_1) pf)
               (@Disks (Some d_0) None ltac:(congruence)).

Definition combined_step := pre_step bg_failure (@op_step).


Module Type TwoDiskBaseAPI.

  Parameter init : prog InitResult.
  Parameter read : diskId -> addr -> prog (DiskResult block).
  Parameter write : diskId -> addr -> block -> prog (DiskResult unit).
  Parameter diskSize : diskId -> prog (DiskResult nat).
  Parameter recover : prog unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall i a, prog_spec (op_spec (combined_step (op_read i a))) (read i a) recover abstr.
  Axiom write_ok : forall i a b, prog_spec (op_spec (combined_step (op_write i a b))) (write i a b) recover abstr.
  Axiom diskSize_ok : forall i, prog_spec (op_spec (combined_step (op_disksize i))) (diskSize i) recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_wipe.

  Hint Resolve init_ok.
  Hint Resolve read_ok.
  Hint Resolve write_ok.
  Hint Resolve diskSize_ok.
  Hint Resolve recover_noop.

End TwoDiskBaseAPI.
