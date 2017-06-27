Require Import Automation.
Require Import Disk.SimpleDisk.
Require Import Omega.

Require Import ReplicatedDisk.ReplicatedDiskAPI.
Require Import ReplicatedDisk.TwoDiskAPI.
Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.


Module ReplicatedDisk.

  Section Implementation.

    Variable (td : Interface TD.API).

    Definition read (a:addr) : prog block :=
      mv0 <- Prim td (TD.Read d0 a);
        match mv0 with
        | Working v => Ret v
        | Failed => mv2 <- Prim td (TD.Read d1 a);
                     match mv2 with
                     | Working v => Ret v
                     | Failed => Ret block0
                     end
        end.

    Definition write (a:addr) (b:block) : prog unit :=
      _ <- Prim td (TD.Write d0 a b);
        _ <- Prim td (TD.Write d1 a b);
        Ret tt.

    Definition diskSize : prog nat :=
      msz <- Prim td (TD.DiskSize d0);
        match msz with
        | Working sz => Ret sz
        | Failed => msz <- Prim td (TD.DiskSize d1);
                     match msz with
                     | Working sz => Ret sz
                     | Failed => Ret 0
                     end
        end.


    Definition rd_op_impl T (op: ReplicatedDisk.Op T) : prog T :=
      match op with
      | ReplicatedDisk.Read a => read a
      | ReplicatedDisk.Write a b => write a b
      | ReplicatedDisk.DiskSize => diskSize
      end.

    Fixpoint init_at (a:nat) : prog unit :=
      match a with
      | 0 => Ret tt
      | S a => _ <- Prim td (TD.Write d0 a block0);
                _ <- Prim td (TD.Write d1 a block0);
                init_at a
      end.

    Definition DiskSizes : prog (nat * nat + nat) :=
      sz1 <- Prim td (TD.DiskSize d0);
        match sz1 with
        | Working sz1 => sz2 <- Prim td (TD.DiskSize d1);
                          match sz2 with
                          | Working sz2 => if sz1 == sz2 then
                                            Ret (inr sz1)
                                          else Ret (inl (sz1, sz2))
                          | Failed => Ret (inr sz1)
                          end
        | Failed => sz2 <- Prim td (TD.DiskSize d1);
                     match sz2 with
                     | Working sz2 => Ret (inr sz2)
                     | Failed => Ret (inl (0, 0)) (* impossible *)
                     end
        end.

    Definition Init : prog InitResult :=
      sizes <- DiskSizes;
        match sizes with
        | inr sz => _ <- init_at sz;
                     Ret Initialized
        | inl _ => Ret InitFailed
        end.

   (* Recovery tracks what happens at each step in order to implement control
       flow. *)
    Inductive RecStatus :=
    (* continue working, nothing interesting has happened *)
    | Continue
    (* some address has been repaired (or the recovery has exhausted the
       addresses) - only one address can be out of sync and thus only it must be
       recovered. *)
    | RepairDone
    (* one of the disks has failed, so don't bother continuing recovery since the
       invariant is now trivially satisfied *)
    | DiskFailed (i:diskId).

    Definition fixup (a:addr) : prog RecStatus :=
      mv0 <- Prim td (TD.Read d0 a);
        match mv0 with
        | Working v => mv2 <- Prim td (TD.Read d1 a);
                        match mv2 with
                        | Working v' => if v == v' then
                                         Ret Continue
                                       else
                                         mu <- Prim td (TD.Write d1 a v);
                                         Ret (match mu with
                                              | Working _ => RepairDone
                                              | Failed => DiskFailed d1
                                              end)
                        | Failed => Ret (DiskFailed d1)
                        end
        | Failed => Ret (DiskFailed d0)
        end.

    (* recursively performs recovery at [a-1], [a-2], down to 0 *)
    Fixpoint recover_at (a:addr) : prog RecStatus :=
      match a with
      | 0 => Ret RepairDone
      | S n => s <- fixup n;
                match s with
                | Continue => recover_at n
                | RepairDone => Ret RepairDone
                | DiskFailed i => Ret (DiskFailed i)
                end
      end.

    Definition Recover : prog unit :=
      sz <- diskSize;
      _  <- recover_at sz;
      Ret tt.

    Definition impl : InterfaceImpl ReplicatedDisk.Op :=
      {| op_impl := rd_op_impl;
         recover_impl := _ <- irec td; Recover;
         init_impl := then_init (iInit td) (Init); |}.

    Definition abstraction_f (td_state : TD.State) : ReplicatedDisk.State :=
      match td_state with
      | TD.Disks (Some d) _ _ => d
      | TD.Disks None (Some d) _ => d
      | _ => empty_disk (* impossible *)
      end.

    Definition rd_invariant (state:TD.State) :=
      match state with
      | TD.Disks (Some d_0) (Some d_1) _ =>
        d_0 = d_1
      | _ => True
      end.

    Definition rd_layer_abstraction (state:TD.State) (state':ReplicatedDisk.State) :=
      rd_invariant state /\
      state' = abstraction_f state.

    Definition abstr : Abstraction ReplicatedDisk.State :=
      abstraction_compose
        (interface_abs td)
        {| abstraction := rd_layer_abstraction |}.

    Definition rd : Interface ReplicatedDisk.API.
      unshelve econstructor.
      - exact impl.
      - exact abstr.
      - intros.
        destruct op; unfold op_spec;
          apply spec_abstraction_compose;
            unfold spec_impl, abstr.
        + unfold prog_spec; intros.

      Unshelve.
      all: eauto.

    Defined.

  End Implementation.

End RemappedDisk.
