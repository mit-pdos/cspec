Require Import Coq.Program.Equality.
Require Import EquivDec.

Require Import Automation.
Require Import Prog.
Require Import ProgTheorems.
Require SequentialDisk.

Set Implicit Arguments.

(** Implementation of a single synchronous disk abstraction using the three
disks for replication. *)

(** vote picks any one of [a1], [a2] and [a3] if it is equal to at least one
other; this implementation is non-trivial, but a more obvious correctness proof
is given below. *)
Definition vote A {AEQ:EqDec A eq} (a1 a2 a3:A) : A :=
  if a2 == a3 then a2 else a1.

Theorem vote_spec : forall A (AEQ:EqDec A eq) a1 a2 a3,
    let a := vote a1 a2 a3 in
    (a1 = a2 -> a = a1) /\
    (a2 = a3 -> a = a2) /\
    (a1 = a3 -> a = a3) /\
    (* specifies the default behavior if there is no majority vote *)
    (a1 <> a2 /\ a2 <> a3 /\ a1 <> a3 -> a = a1).
Proof.
  unfold vote; intros.
  destruct (a2 == a3); intuition.
Qed.

Lemma vote_eq : forall A {AEQ:EqDec A eq} a a',
    vote a a a' = a.
Proof.
  unfold vote; intros.
  destruct matches.
Qed.

Definition RRead_impl (a:addr) : prog3 block :=
  v0 <- Read d0 a;
    v1 <- Read d1 a;
    v2 <- Read d2 a;
    Ret (vote v0 v1 v2).

Definition RWrite_impl (a:addr) (b:block) : prog3 unit :=
  _ <- Write d0 a b;
    _ <- Write d1 a b;
    Write d2 a b.

Import SequentialDisk.

Fixpoint translate T (p: prog T) : prog3 T :=
 match p with
 | SRead a => RRead_impl a
 | SWrite a b => RWrite_impl a b
 | Ret v => Prog.Ret v
 | Bind p p' => Prog.Bind (translate p)
                         (fun r => translate (p' r))
 end.

(** We will now show a simulation between the single-disk semantics and
single-disk programs implemented using replication on top of a 3-disk
configuration.

The idea of this proof is that correctness of a prog in terms of the
supposed single-disk semantics should carry over to correctness of the
translated program (which implements a sequential program using replication).
The proof will show that from a pair of related states, any behavior of the
prog can be re-produced as related behavior in the translated prog3.
 *)

(* The simulation is defined in terms of relating the states of the two
programs. Our relation captures replicated configurations line up with a
sequential disk. *)
Definition pstate_rel (spstate:SPState) (pstate:PState) : Prop :=
  forall a, match sdisk spstate a with
       | Some v => exists v0 v1 v2,
                  disk0 pstate a = Some v0 /\
                  disk1 pstate a = Some v1 /\
                  disk2 pstate a = Some v2 /\
                  v = vote v0 v1 v2
       | None => disk0 pstate a = None /\
                disk1 pstate a = None /\
                disk2 pstate a = None
       end.

Inductive result_rel PState1 PState2 (rel: PState1 -> PState2 -> Prop) T :
  Result PState1 T -> Result PState2 T -> Prop :=
| Finished_rel : forall pstate1 pstate2 v,
    rel pstate1 pstate2 ->
    result_rel rel (Finished v pstate1) (Finished v pstate2)
(* there is one more valid simulation: if the first relation succeeds, then it's
   ok for the second to fail, in the order PState1 and PState2 are given here. *)
| Crashed_rel : forall pstate1 pstate2,
    rel pstate1 pstate2 ->
    (* this is too strong: should be able to state any relation for crash states
    and then fix things up in recovery *)
    result_rel rel (Crashed pstate1) (Crashed pstate2)
| Failed_rel : result_rel rel Failed Failed.

Hint Constructors result_rel.
Hint Constructors Prog.exec.

(* TODO: cleanup these almost Hoare specs:

 move them into a BasicSpecs file, and probably make them proper Hoare
 quadruples *)

Lemma Read_ok : forall i a pstate r,
    Prog.exec (Read i a) pstate r ->
    match r with
    | Finished v pstate' => disk_id i pstate a = Some v /\
                           pstate' = pstate
    | Crashed pstate' => pstate' = pstate
    | Failed => disk_id i pstate a = None
    end.
Proof.
  intros.
  inv_exec; try simp_stepto; intuition eauto.
Qed.

Lemma Write_ok : forall i a b pstate r,
    Prog.exec (Write i a b) pstate r ->
    match r with
    | Finished v pstate' => (exists v0, disk_id i pstate a = Some v0) /\
                           pstate' = upd_disk i pstate (fun d => Mem.upd d a b)
    | Crashed pstate' => pstate' = pstate \/
                        pstate' = upd_disk i pstate (fun d => Mem.upd d a b)
    | Failed => disk_id i pstate a = None
    end.
Proof.
  intros.
  inv_exec; try simp_stepto; intuition eauto.
Qed.

Lemma RRead_impl_ok : forall a pstate r,
    Prog.exec (RRead_impl a) pstate r ->
    match r with
    | Finished v pstate' => (exists v0 v1 v2, disk0 pstate a = Some v0 /\
                           disk1 pstate a = Some v1 /\
                           disk2 pstate a = Some v2 /\
                           v = vote v0 v1 v2) /\
                           pstate' = pstate
    | Crashed pstate' => pstate' = pstate
    | Failed => (disk0 pstate a = None \/
                disk1 pstate a = None \/
                disk2 pstate a = None)
    end.
Proof.
  unfold RRead_impl; intros.

  eapply exec_bind in H.
  intuition; repeat deex;
    match goal with
    | [ H: Prog.exec (Read _ _) _ _ |- _ ] =>
      apply Read_ok in H; safe_intuition;
        cbn [disk_id] in *; subst
    end; auto.

  eapply exec_bind in H0;
    intuition; repeat deex;
      match goal with
      | [ H: Prog.exec (Read _ _) _ _ |- _ ] =>
        apply Read_ok in H; safe_intuition;
          cbn [disk_id] in *; subst
      end; auto.

  eapply exec_bind in H1;
    intuition; repeat deex;
      match goal with
      | [ H: Prog.exec (Read _ _) _ _ |- _ ] =>
        apply Read_ok in H; safe_intuition;
          cbn [disk_id] in *; subst
      end; auto.

  apply exec_ret in H2.
  destruct r; intuition.
  subst; descend; intuition eauto.
Qed.

Lemma opts_eq : forall T a (v v':T),
    a = Some v ->
    a = Some v' ->
    v = v'.
Proof.
  intros; subst.
  inversion H0; auto.
Qed.

Lemma opt_discriminate : forall T a (v:T),
    a = Some v ->
    a = None ->
    False.
Proof.
  intros; subst.
  discriminate.
Qed.

Hint Constructors exec.

Ltac inv_rel :=
  match goal with
  | [ H: result_rel _ _ _ |- _ ] =>
    inversion H; subst; clear H
  end.

Theorem translate_exec : forall T (p: prog T),
    forall pstate r,
      Prog.exec (translate p) pstate r ->
      forall spstate, pstate_rel spstate pstate ->
                 exists sr, exec p spstate sr /\
                       result_rel pstate_rel sr r.
Proof.
  induction p; simpl; intros.
  - apply RRead_impl_ok in H.
    pose proof (H0 a).
    destruct (sdisk spstate a) eqn:?;
             repeat deex.
    destruct r; safe_intuition; repeat deex; subst; eauto.
    repeat match goal with
           | [ H: ?a = Some _, H': ?a = Some _ |- _ ] =>
             pose proof (opts_eq H H');
               clear H';
               subst
           end.
    exists (Finished (vote v0 v1 v2) spstate);
      intuition eauto.
    eapply ExecStepTo; simpl; simpl_match; eauto.
    intuition;
      solve [ exfalso; eauto using opt_discriminate ].

    destruct r; safe_intuition; repeat deex; subst; eauto.
    solve [ exfalso; eauto using opt_discriminate ].
    clear H.
    exists Failed; intuition eauto.
    eapply ExecStepFail; simpl; simpl_match; auto.
  - admit.
  - apply exec_ret in H.
    destruct r; safe_intuition; subst; eauto.
    exists (Finished v0 spstate); intuition eauto.
    exists Failed; intuition eauto.
  - eapply exec_bind in H0; intuition; repeat deex; subst.
    + specialize (IHp _ _ ltac:(eauto) _ ltac:(eauto)).
      repeat deex; inv_rel.
      specialize (H _ _ _ ltac:(eauto) _ ltac:(eauto)).
      repeat deex.
      eauto.
    + specialize (IHp _ _ ltac:(eauto) _ ltac:(eauto)).
      repeat deex; inv_rel.
      eauto.
    + specialize (IHp _ _ ltac:(eauto) _ ltac:(eauto)).
      repeat deex; inv_rel.
      eauto.
Admitted.

Inductive rresult_rel PState1 PState2 (rel: PState1 -> PState2 -> Prop) T R :
  RResult PState1 T R -> RResult PState2 T R -> Prop :=
| RFinished_rel : forall pstate1 pstate2 v,
    rel pstate1 pstate2 ->
    rresult_rel rel (RFinished v pstate1) (RFinished v pstate2)
(* TODO: as above, add rresult_rel Finished Fail *)
| Recovered_rel : forall pstate1 pstate2 r,
    rel pstate1 pstate2 ->
    rresult_rel rel (Recovered r pstate1) (Recovered r pstate2)
| RFailed_rel : rresult_rel rel RFailed RFailed.

Hint Constructors rresult_rel.
Hint Constructors exec_recover.

Lemma RExecCrash_eq : forall T R (p: prog T) (rec: prog R)
                        pstate pstate' r r',
    exec p pstate (Crashed pstate') ->
    exec_recover rec rec pstate' r ->
    r' = to_recovered r ->
    exec_recover p rec pstate r'.
Proof.
  intros; subst.
  eauto.
Qed.

Hint Resolve RExecCrash_eq.

Ltac apply_translate :=
match goal with
      | [ H: Prog.exec (translate _) ?s _,
             H': pstate_rel _ ?s |- _ ] =>
        eapply translate_exec in H; eauto;
          repeat deex; repeat inv_rel
      end.

Lemma to_recovered_idempotent : forall T R PState (r: RResult PState R R),
    to_recovered (T:=T) (to_recovered (T:=R) r) = to_recovered r.
Proof.
  destruct r; simpl; eauto.
Qed.

Theorem translate_exec_self_recover : forall R (rec: prog R),
    forall pstate r,
      Prog.exec_recover (translate rec) (translate rec) pstate r ->
      forall spstate, pstate_rel spstate pstate ->
                exists sr, exec_recover rec rec spstate sr /\
                      rresult_rel pstate_rel sr r.
Proof.
  intros.
  generalize dependent spstate.
  dependent induction H; simpl; intros;
    apply_translate.
  - exists (RFinished v pstate1); intuition eauto.
  - exists (RFailed); intuition eauto.
  - specialize (IHexec_recover rec r0).
    repeat match type of IHexec_recover with
           | ?P -> _ =>
             lazymatch type of P with
             | Prop => specialize (IHexec_recover ltac:(auto))
             | _ => idtac
             end
           end.
    admit. (* this seems to require some idempotence of the prog recovery
    procedure - surprising, but maybe it's required? *)
Admitted.

Lemma rresult_rel_recovered : forall PState1 PState2 rel T R
                                (r: RResult PState1 R R)
                                (r': RResult PState2 R R),
    rresult_rel rel r r' ->
    rresult_rel (T:=T) rel (to_recovered r) (to_recovered r').
Proof.
  intros.
  inversion H; subst; simpl; eauto.
Qed.

Hint Resolve rresult_rel_recovered.

Theorem translate_exec_recover : forall T R (p: prog T) (rec: prog R),
    forall pstate r,
      (* NOTE: the equivalent recovery procedure is more generally run before
      [translate rec]. However, we need some way to handoff the recovered memory
      state to [fun v => translate (rec v)] while also making [rec] a complete
      program in [prog]. *)
      Prog.exec_recover (translate p) (translate rec) pstate r ->
      forall spstate, pstate_rel spstate pstate ->
                exists sr, exec_recover p rec spstate sr /\
                      rresult_rel pstate_rel sr r.
Proof.
  intros.
  remember (translate p).
  remember (translate rec).
  destruct H; simpl; intros; subst.
  - apply_translate.
    descend; intuition eauto.
  - apply_translate.
    descend; intuition eauto.
  - apply_translate.
    eapply translate_exec_self_recover in H1; eauto;
      repeat deex.
    exists (to_recovered sr); intuition eauto.
Qed.