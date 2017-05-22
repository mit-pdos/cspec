Require Import Disk.
Require Import Automation.

Require Import Refinement.ProgLang.Prog.
Require Import Refinement.ProgLang.Hoare.
Require Import TwoDisk.TwoDiskAPI.
Require Import SeqDisk.SeqDiskAPI.

Require Import SeqDisk.ReplicatedDisk.Step.
Require Import SeqDisk.ReplicatedDisk.DiskSize.
Require Import SeqDisk.ReplicatedDisk.Recovery.
Require Import SeqDisk.ReplicatedDisk.ReadWrite.

Require Import MaybeHolds.
Require Import Refinement.Interface.

(* The replicated disk implementation of the SeqDiskAPI (D.API) using two disks,
despite failures at the two disk level. *)

Module RD.

  Section ReplicatedDisk.

    (* The replicated disk implementation works for any implementation of two
    disks - [Interface] already captures the implementation and all the
    correctness proofs needed here. *)
    Variable (td:Interface TD.API).

    (* As the final step in giving the correctness of the replicated disk
    operations, we prove recovery specs that include the replicated disk Recover
    function. *)

    Ltac start := intros;
                  match goal with
                  | |- prog_rspec _ _ (_ <- _; _) _ =>
                    eapply compose_recovery; eauto; simplify
                  end.

    (* it's sufficient to use regular hints to plug these specifications into
    the basic automation here *)
    Hint Resolve Read_ok Write_ok DiskSize_ok Recover_ok.

    Theorem Read_rok : forall a,
        prog_rspec
          (fun d state =>
             {|
               pre := TD.disk0 state |= eq d /\
                      TD.disk1 state |= eq d;
               post :=
                 fun r state' =>
                   d a |= eq r /\
                   TD.disk0 state' |= eq d /\
                   TD.disk1 state' |= eq d;
               recover :=
                 fun _ state' =>
                   TD.disk0 state' |= eq d /\
                   TD.disk1 state' |= eq d;
             |})
          (Read td a) (_ <- irec td; Recover td)
          (refinement td).
    Proof.
      start.
      rename a0 into d.
      descend; (intuition eauto); simplify.
      exists d, FullySynced; intuition eauto.
    Qed.

    Theorem Write_rok : forall a b,
        prog_rspec
          (fun d state =>
             {|
               pre :=
                 TD.disk0 state |= eq d /\
                 TD.disk1 state |= eq d;
               post :=
                 fun r state' =>
                   r = tt /\
                   TD.disk0 state' |= eq (diskUpd d a b) /\
                   TD.disk1 state' |= eq (diskUpd d a b);
               recover :=
                 fun _ state' =>
                   (TD.disk0 state' |= eq d /\
                    TD.disk1 state' |= eq d) \/
                   (TD.disk0 state' |= eq (diskUpd d a b) /\
                    TD.disk1 state' |= eq (diskUpd d a b));
             |})
          (Write td a b) (_ <- irec td; Recover td)
          (refinement td).
    Proof.
      start.
      rename a0 into d.
      descend; (intuition eauto); simplify.
      - exists d, FullySynced; intuition eauto.
      - exists d, (OutOfSync a b); intuition eauto.
      - exists (diskUpd d a b), FullySynced; intuition eauto.
    Qed.

    Theorem DiskSize_rok :
      prog_rspec
        (fun d state =>
           {|
             pre := TD.disk0 state |= eq d /\
                    TD.disk1 state |= eq d;
             post :=
               fun r state' =>
                 r = size d /\
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
             recover :=
               fun _ state' =>
                 TD.disk0 state' |= eq d /\
                 TD.disk1 state' |= eq d;
           |})
        (DiskSize td) (_ <- irec td; Recover td)
        (refinement td).
    Proof.
      eapply compose_recovery; eauto.
      eapply prog_rok_to_rspec; [ eapply DiskSize_ok | eauto | simplify ].
      simplify.

      rename a into d.
      exists d, d; (intuition eauto); simplify.
      exists d, FullySynced; intuition eauto.
    Qed.

    (* Now we gather up the implementation and all the correctness proofs,
    expressing them in terms of the high-level API in D.API. *)

    (* First, we prove some lemmas that re-express the D.API semantics in more
    convenient terms (in some cases, just for the sake of the automation). *)

    Lemma read_step : forall a (state state':D.State) b,
        state a |= eq b ->
        state' = state ->
        D.step (D.Read a) state b state'.
    Proof.
      intros; subst.
      constructor; auto.
      intros.
      replace (state a) in *; auto.
    Qed.

    Lemma write_step : forall a b (state state':D.State) u,
        state' = diskUpd state a b ->
        D.step (D.Write a b) state u state'.
    Proof.
      intros; subst.
      destruct u.
      econstructor; eauto.
    Qed.

    Lemma disk_size_step : forall (state state':D.State) r,
        r = size state ->
        state' = state ->
        D.step (D.DiskSize) state r state'.
    Proof.
      intros; subst.
      econstructor; eauto.
    Qed.

    Hint Resolve read_step write_step disk_size_step.

    (* The proof will require a refinement; we build one up based on the two
    disk state. *)

    Definition rd_abstraction (state:TD.State) : D.State :=
      match state with
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

    (* We re-express the abstraction and invariant's behavior in terms of the
       maybe holds (m |= F) statements in all of our specifications. *)

    Ltac crush :=
      intros; repeat match goal with
                     | [ state: TD.State |- _ ] =>
                       destruct state; simpl in *
                     | _ => destruct matches in *
                     | _ => eauto
                     end.

    Lemma invariant_to_disks_eq0 : forall state,
        rd_invariant state ->
        TD.disk0 state |= eq (rd_abstraction state).
    Proof.
      crush.
    Qed.

    Lemma invariant_to_disks_eq1 : forall state,
        rd_invariant state ->
        TD.disk1 state |= eq (rd_abstraction state).
    Proof.
      crush.
    Qed.

    Lemma disks_eq_to_invariant : forall state d,
        TD.disk0 state |= eq d ->
        TD.disk1 state |= eq d ->
        rd_invariant state.
    Proof.
      crush.
    Qed.

    Lemma disks_eq_to_abstraction : forall state d,
        TD.disk0 state |= eq d ->
        TD.disk1 state |= eq d ->
        rd_abstraction state = d.
    Proof.
      crush.
      solve_false.
    Qed.

    Hint Resolve invariant_to_disks_eq0 invariant_to_disks_eq1.
    Hint Resolve disks_eq_to_invariant disks_eq_to_abstraction.

    (* Finally, we put together the pieces of the [Interface]. Here we also
    convert from our specificatiosn above to the exact form that an Interface
    uses; the proofs are automatic after defining the lemmas above about D.step
    and the layer refinement. *)

    Definition d_op_impl T (op:D.Op T) : prog T :=
      match op with
      | D.Read a => Read td a
      | D.Write a b => Write td a b
      | D.DiskSize => DiskSize td
      end.

    Definition rd_refinement :=
      refinement_compose
        (refinement td)
        {| invariant := rd_invariant;
           abstraction := rd_abstraction; |}.

    Definition impl : InterfaceImpl D.Op :=
      {| op_impl := d_op_impl;
         recover_impl := _ <- irec td; Recover td; |}.

    Hint Resolve Read_rok Write_rok DiskSize_rok Recover_rok.

    Definition rd : Interface D.API.
      unshelve econstructor.
      - exact impl.
      - exact rd_refinement.
      - intros.
        destruct op; unfold op_spec;
          apply rspec_refinement_compose;
          eapply prog_rspec_weaken; eauto;
            unfold rspec_impl; simplify.
        + exists (rd_abstraction state); (intuition eauto); simplify.
        + exists (rd_abstraction state); (intuition eauto); simplify.
        + exists (rd_abstraction state); (intuition eauto); simplify.
      - eapply rec_noop_compose; eauto; simpl.
        eapply prog_rspec_weaken; eauto;
          unfold rspec_impl; simplify.
        exists (rd_abstraction state), FullySynced; intuition eauto.

        Grab Existential Variables.
        all: auto.
    Defined.

    (* For the convenience of the extracted Haskell code we define short
    functions to access the final implementation. *)

    Definition prim T (op: D.Op T) : prog T :=
      Prim rd op.

    Definition recover : prog unit :=
      irec rd.

  End ReplicatedDisk.

End RD.
