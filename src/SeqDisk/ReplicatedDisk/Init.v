Require Import Automation.
Require Import Disk.

Require Import Refinement.Interface.
Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import TwoDisk.TwoDiskAPI.
Require Import TwoDisk.TwoDiskTheorems.
Require Import
        SeqDisk.ReplicatedDisk.Step
        SeqDisk.ReplicatedDisk.TwoDiskFacts.

Require Import MaybeHolds.

Section Init.

  Variable (td:Interface TD.API).

  Fixpoint init_at (a:nat) : prog unit :=
    match a with
    | 0 => Ret tt
    | S a => _ <- Prim td (TD.Write d0 a block0);
              _ <- Prim td (TD.Write d1 a block0);
              init_at a
    end.

  Definition Init : prog InitResult :=
    sz1 <- Prim td (TD.DiskSize d0);
      match sz1 with
      | Working sz1 => sz2 <- Prim td (TD.DiskSize d1);
                        match sz2 with
                        | Working sz2 => if sz1 == sz2 then
                                          _ <- init_at sz1;
                                            Ret Initialized
                                        else Ret InitFailed
                        | Failed => _ <- init_at sz1;
                                     Ret Initialized
                        end
      | Failed => sz2 <- Prim td (TD.DiskSize d1);
                   match sz2 with
                   | Working sz2 => _ <- init_at sz2;
                                     Ret Initialized
                   | Failed => Ret InitFailed (* impossible *)
                   end
      end.

End Init.
