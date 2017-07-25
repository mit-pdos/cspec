Require Import POCS.
Require Import AtomicPair.AtomicPairAPI.
Require Import OneDisk.OneDiskAPI.

Import OneDisk.
Import AtomicPair.

Module AtomicPair.

  Section Implementation.

    Variable (d : Interface OneDisk.API).

    Definition get : prog (block*block) :=
      ptr <- Prim d (Read 0);
      if ptr == block0 then
        a <- Prim d (Read 1);
        b <- Prim d (Read 2);
        Ret (a, b)
      else
        a <- Prim d (Read 3);
        b <- Prim d (Read 4);
        Ret (a, b).

    Definition put (p : block*block) : prog unit :=
      ptr <- Prim d (Read 0);
      if ptr == block0 then
        _ <- Prim d (Write 3 (fst p));
        _ <- Prim d (Write 4 (snd p));
        _ <- Prim d (Write 0 block1);
        Ret tt
      else
        _ <- Prim d (Write 1 (fst p));
        _ <- Prim d (Write 2 (snd p));
        _ <- Prim d (Write 0 block0);
        Ret tt.

    Definition ap_op_impl T (op: AtomicPair.Op T) : prog T :=
      match op with
      | Get => get
      | Put p => put p
      end.

    Definition init : prog InitResult :=
      len <- Prim d (DiskSize);
      if len == 5 then
        _ <- Prim d (Write 0 block0);
        Ret Initialized
      else
        Ret InitFailed.

    Definition impl : InterfaceImpl AtomicPair.Op :=
      {| op_impl := ap_op_impl;
         recover_impl := irec d;
         init_impl := then_init (iInit d) init; |}.

    Definition atomic_pair_abstraction (ds : OneDisk.State) (ps : AtomicPair.State) : Prop :=
      size ds = 5 /\
      (ds 0 = Some block0 /\ ds 1 = Some (fst ps) /\ ds 2 = Some (snd ps) \/
       ds 0 = Some block1 /\ ds 3 = Some (fst ps) /\ ds 4 = Some (snd ps)).

    Definition abstr : Abstraction AtomicPair.State :=
      abstraction_compose
        (interface_abs d)
        {| abstraction := atomic_pair_abstraction |}.

    Definition ap : Interface AtomicPair.API.
      unshelve econstructor.
      - exact impl.
      - exact abstr.
      - destruct op.

        + lift_world.

          (* first read of the pointer *)
          eapply prog_spec_rx; [ apply impl_ok | ].
          intro x; destruct x; simpl; intros.

          exists tt; intuition auto.

          2: unfold crash_relation, OneDisk.crash_relation in *; subst; repeat deex; repeat inv_step; eexists; intuition auto.
          2: unfold crash_relation, OneDisk.crash_relation in *; subst; repeat deex; repeat inv_step; eexists; intuition auto.

          (* branch on the if statement *)
          destruct (r == block0); subst.

          (* first read on the block0 branch *)
          eapply prog_spec_rx; [ apply impl_ok | ].
          simpl; intros.

          exists tt; intuition auto.

          2: unfold crash_relation, OneDisk.crash_relation in *; subst; repeat deex; repeat inv_step; eexists; intuition auto.
          2: unfold crash_relation, OneDisk.crash_relation in *; subst; repeat deex; repeat inv_step; eexists; intuition auto.

          (* second read on the block0 branch *)
          eapply prog_spec_rx; [ apply impl_ok | ].
          simpl; intros.

          exists tt; intuition auto.

          2: unfold crash_relation, OneDisk.crash_relation in *; subst; repeat deex; repeat inv_step; eexists; intuition auto.
          2: unfold crash_relation, OneDisk.crash_relation in *; subst; repeat deex; repeat inv_step; eexists; intuition auto.

          (* return on the block0 branch *)
          eapply ret_spec.
          eapply ret_rec_ok.
          simpl; intros; intuition auto.

          eexists; split; [ constructor | ].

          (* doable but messy... *)


          prog_spec_symbolic_execute inv_step.

          all: pose block0_block1_differ.
          all: unfold atomic_pair_abstraction in *; intuition auto.
          all: try solve [ exfalso; eapply disk_inbounds_not_none; eauto; omega ].
          all: try congruence.

          * solve_final_state.

            destruct s; simpl in *; congruence.
            intuition congruence.

          * solve_final_state.

            destruct s; simpl in *; congruence.
            intuition congruence.

        + lift_world.
          prog_spec_symbolic_execute inv_step.

          all: pose block0_block1_differ.
          all: unfold atomic_pair_abstraction in *; intuition auto.
          all: try congruence.

          * solve_final_state.
            repeat autorewrite with upd.
            repeat ( ( rewrite diskUpd_eq by ( repeat rewrite diskUpd_size; omega ) ) ||
                     rewrite diskUpd_neq by congruence ).
            intuition auto.

          * solve_final_state.
            repeat autorewrite with upd.
            repeat ( ( rewrite diskUpd_eq by ( repeat rewrite diskUpd_size; omega ) ) ||
                     rewrite diskUpd_neq by congruence ).
            intuition auto.

      - unfold rec_noop; intros.
        lift_world.
        prog_spec_symbolic_execute inv_step.
        solve_final_state; intuition eauto.

      - eapply then_init_compose; eauto.
        prog_spec_symbolic_execute inv_step.

        + case_eq (state' 1); intros; [ | exfalso ].
          case_eq (state' 2); intros; [ | exfalso ].

          solve_final_state.
          autorewrite with upd; auto.
          repeat ( ( rewrite diskUpd_eq by ( repeat rewrite diskUpd_size; omega ) ) ||
                   rewrite diskUpd_neq by congruence ).
          instantiate (1 := (b, b0)).
          intuition auto.

          eapply disk_inbounds_not_none; eauto; omega.
          eapply disk_inbounds_not_none; eauto; omega.

        + match_abstraction_for_step; auto.

      Grab Existential Variables.
      all: eauto.

    Defined.

  End Implementation.

End AtomicPair.

Print Assumptions AtomicPair.ap.
