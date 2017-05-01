Require Import FunctionalExtensionality.

Require Import Disk.
Require Import Automation.

Require Import Shallow.ProgLang.Prog.
Require Import Shallow.ProgLang.Hoare.
Require Import Shallow.TwoDiskProg.
Require Import Shallow.SeqDiskProg.

Require Import Interpret.

Module RD.

  Definition Read (a:addr) : TD.prog block :=
    mv0 <- Prim (TD.Read d0 a);
      match mv0 with
      | Working v => Ret v
      | Failed => mv2 <- Prim (TD.Read d1 a);
                   match mv2 with
                   | Working v => Ret v
                   | Failed => Ret block0
                   end
      end.

  Definition Write (a:addr) (b:block) : TD.prog unit :=
    _ <- Prim (TD.Write d0 a b);
      _ <- Prim (TD.Write d1 a b);
      Ret tt.

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

  Definition fixup (a:addr) : TD.prog RecStatus :=
    mv0 <- Prim (TD.Read d0 a);
      match mv0 with
      | Working v => mv2 <- Prim (TD.Read d1 a);
                      match mv2 with
                      | Working v' => if v == v' then
                                       Ret Continue
                                     else
                                       mu <- Prim (TD.Write d1 a v);
                                       Ret (match mu with
                                            | Working _ => RepairDone
                                            | Failed => DiskFailed d1
                                            end)
                      | Failed => Ret (DiskFailed d1)
                      end
      | Failed => Ret (DiskFailed d0)
      end.

  (* recursively performs recovery at [a-1], [a-2], down to 0 *)
  Fixpoint recover_at (a:addr) : TD.prog RecStatus :=
    match a with
    | 0 => Ret RepairDone
    | S n => s <- fixup n;
              match s with
              | Continue => recover_at n
              | RepairDone => Ret RepairDone
              | DiskFailed i => Ret (DiskFailed i)
              end
    end.

  (* recovery for a disk of size [sz] *)
  Definition Recover (sz:nat) : TD.prog unit :=
    _ <- recover_at sz;
      Ret tt.

  Definition op_impl T (op:D.Op T) : TD.prog T :=
    match op with
    | D.Read a => Read a
    | D.Write a b => Write a b
    end.

  Definition interpret := Interpret.interpret op_impl.

  Definition abstraction (state:TD.State) : D.State :=
    match state with
    | TD.Disks (Some d) _ _ => D.Disk d
    | TD.Disks None (Some d) _ => D.Disk d
    | _ => D.Disk empty_disk (* impossible *)
    end.

  Definition invariant (state:TD.State) :=
    match state with
    | TD.Disks (Some d_0) (Some d_1) _ =>
      d_0 = d_1
    | _ => True
    end.

  Theorem RD_ok : interpretation
                    op_impl
                    TD.step D.step
                    invariant
                    abstraction.
  Proof.
    eapply interpret_exec; intros; eauto.
    - destruct op; simpl in *.
      + admit.
      + admit.
    - destruct op in *; simpl in *.
      + admit.
      + admit.
  Abort.

End RD.
