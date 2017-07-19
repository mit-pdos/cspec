Require Export Disk.Sectors.

Set Implicit Arguments.

Inductive diskId := d0 | d1.

Inductive DiskResult T :=
| Working (v:T)
| Failed.

Arguments Failed {T}.

Module TD.

  Inductive Op : Type -> Type :=
  | Read (i:diskId) (a:addr) : Op (DiskResult block)
  | Write (i:diskId) (a:addr) (b:block) : Op (DiskResult unit)
  | Sync (i:diskId) : Op (DiskResult unit)
  (* get disk size in blocks *)
  | DiskSize (i:diskId) : Op (DiskResult nat).

  Section TwoDiskState.

    (** The state the program manipulates as it executes. *)
    Record State diskT :=
      Disks { disk0 : option diskT;
              disk1 : option diskT;
              some_disk_works : disk0 = None -> disk1 = None -> False }.

    Arguments Disks {diskT} disk0 disk1 some_disk_works.

    (** Get a particular disk from a state by id. *)
    Definition get_disk {diskT} (i:diskId) (state:State diskT) : option diskT :=
      match i with
      | d0 => disk0 state
      | d1 => disk1 state
      end.

    Local Lemma d0_is_some {diskT} (d_0: diskT) (d_1: option diskT) :
      Some d_0 = None -> d_1 = None -> False.
    Proof.
      congruence.
    Qed.

    Local Lemma d1_is_some {diskT} (d_0: option diskT) (d_1: diskT) :
      d_0 = None -> Some d_1 = None -> False.
    Proof.
      congruence.
    Qed.

    Local Notation proof := (ltac:(first [ apply d0_is_some | apply d1_is_some ])) (only parsing).

    Definition set_disk {diskT} (i:diskId) (state:State diskT) (d:diskT) : State diskT :=
      match i with
      | d0 => Disks (Some d) (disk1 state) proof
      | d1 => Disks (disk0 state) (Some d) proof
      end.

    Inductive bg_failure {diskT} : State diskT -> State diskT -> Prop :=
    | step_id : forall state, bg_failure state state
    | step_fail0 : forall d_0 d_1 pf,
        bg_failure (Disks (Some d_0) (Some d_1) pf)
                   (Disks None (Some d_1) proof)
    | step_fail1 : forall d_0 d_1 pf,
        bg_failure (Disks (Some d_0) (Some d_1) pf)
                   (Disks (Some d_0) None proof).

    (* apply a relation to the disks that are present *)
    Inductive disks_rel {diskT} {rel: diskT -> diskT -> Prop} :
      State diskT -> State diskT -> Prop :=
    | both_disks_rel : forall d_0 d_1 d_0' d_1' pf,
        rel d_0 d_0' ->
        rel d_1 d_1' ->
        disks_rel (Disks (Some d_0) (Some d_1) pf)
                  (Disks (Some d_0') (Some d_1') proof)
    | disk0_rel : forall d_0 d_0' pf,
        rel d_0 d_0' ->
        disks_rel (Disks (Some d_0) None pf)
                  (Disks (Some d_0') None proof)
    | disk1_rel : forall d_1 d_1' pf,
        rel d_1 d_1' ->
        disks_rel (Disks None (Some d_1) pf)
                  (Disks None (Some d_1') proof).

    Definition disks_map {diskT} (f: diskT -> diskT) (state: State diskT) : State diskT :=
      match state with
      | Disks (Some d_0) (Some d_1) pf => Disks (Some (f d_0)) (Some (f d_1)) proof
      | Disks (Some d_0) None pf => Disks (Some (f d_0)) None proof
      | Disks None (Some d_1) pf => Disks None (Some (f d_1)) proof
      | _ => state
      end.

  End TwoDiskState.

  Arguments Disks {diskT} disk0 disk1 some_disk_works.
  Arguments disks_rel {diskT} rel state state'.

End TD.