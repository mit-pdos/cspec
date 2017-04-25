Require Import Coq.Program.Equality.
Require Import EquivDec.

Require Import Automation.
Require Import Prog.
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

Fixpoint translate T (p: seq_prog T) : prog3 T :=
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

The idea of this proof is that correctness of a seq_prog in terms of the
supposed single-disk semantics should carry over to correctness of the
translated program (which implements a sequential program using replication).
The proof will show that from a pair of related states, any behavior of the
seq_prog can be re-produced as related behavior in the translated prog3.
 *)

(* The simulation is defined in terms of relating the states of the two
programs. Our relation captures replicated configurations line up with a
sequential disk. *)
Definition sigma_rel (ssigma:SSigma) (sigma:Sigma) : Prop :=
  forall a, match sdisk ssigma a with
       | Some v => exists v0 v1 v2,
                  disk0 sigma a = Some v0 /\
                  disk1 sigma a = Some v1 /\
                  disk2 sigma a = Some v2 /\
                  v = vote v0 v1 v2
       | None => disk0 sigma a = None /\
                disk1 sigma a = None /\
                disk2 sigma a = None
       end.

Inductive result_rel Sigma1 Sigma2 (rel: Sigma1 -> Sigma2 -> Prop) T :
  Result Sigma1 T -> Result Sigma2 T -> Prop :=
| Finished_rel : forall sigma1 sigma2 v,
    rel sigma1 sigma2 ->
    result_rel rel (Finished v sigma1) (Finished v sigma2)
(* there is one more valid simulation: if the first relation succeeds, then it's
   ok for the second to fail, in the order Sigma1 and Sigma2 are given here. *)
| Crashed_rel : forall sigma1 sigma2,
    rel sigma1 sigma2 ->
    (* this is too strong: should be able to state any relation for crash states
    and then fix things up in recovery *)
    result_rel rel (Crashed sigma1) (Crashed sigma2)
| Failed_rel : result_rel rel Failed Failed.

Hint Constructors Prog.exec.
Hint Constructors result_rel.

Ltac prog_bind :=
  eapply Prog.ExecBindFinished.
Ltac prog_step :=
  first [ eapply Prog.ExecStepTo ||
                 eapply Prog.ExecStepFail ];
  simpl; simpl_match; eauto.

Theorem translate_exec : forall T (p: seq_prog T),
    forall ssigma sr,
      exec p ssigma sr -> forall sigma,
        sigma_rel ssigma sigma ->
        exists r, Prog.exec (translate p) sigma r /\
             result_rel sigma_rel sr r.
Proof.
  induction 1; intros.
  - destruct p; simpl in *;
      destruct matches in *;
      match goal with
      | [ H: _ = StepTo _ _ |- _ ] =>
        inversion H; subst; clear H
      end.
    + exists (Finished v sigma0); intuition.
      specialize (H0 a); simpl_match;
        repeat deex.
      unfold RRead_impl.
      repeat (prog_bind; [ prog_step | ]); eauto.
    + pose proof (H0 a); simpl_match;
        repeat deex.
      destruct sigma0; simpl in *; subst.
      refine (ex_intro _ (Finished _ _) _); split.
      repeat (prog_bind; [ prog_step | ]).
      prog_step.

      constructor.
      unfold sigma_rel; intros; simpl.
      destruct (is_eq a a0); subst;
        autorewrite with upd.
      descend; intuition eauto.
      rewrite vote_eq; auto.
      specialize (H0 a0).
      destruct (sdisk sigma a0);
        simpl in *; repeat deex.
      descend; intuition eauto.
      intuition.
    + exists (Finished v sigma0); intuition.
  - destruct p; simpl in *;
      destruct matches in *;
      match goal with
      | [ H: _ = Fails |- _ ] =>
        inversion H; subst; clear H
      end.
    exists Failed; intuition.
    specialize (H0 a); simpl_match; intuition.
    unfold RRead_impl.
    eapply Prog.ExecBindFailed; prog_step.

    exists Failed; intuition.
    specialize (H0 a); simpl_match; intuition.
    unfold RRead_impl.
    eapply Prog.ExecBindFailed; prog_step.

  - destruct p; simpl in *;
      destruct matches in *;
      match goal with
      | [ H: _ = StepTo _ _ |- _ ] =>
        inversion H; subst; clear H
      end.
    + exists (Crashed sigma0); intuition.
    + pose proof (H0 a); simpl_match;
        repeat deex.
      destruct sigma0; simpl in *; subst.
      refine (ex_intro _ (Crashed _) _); split.
      repeat (prog_bind; [ prog_step | ]).
      eapply Prog.ExecCrashAfter; simpl; simpl_match; eauto.

      constructor.
      unfold sigma_rel; intros; simpl.
      destruct (is_eq a a0); subst;
        autorewrite with upd.
      descend; intuition eauto.
      rewrite vote_eq; auto.
      specialize (H0 a0).
      destruct (sdisk sigma a0);
        simpl in *; repeat deex.
      descend; intuition eauto.
      intuition.
    + descend; intuition eauto.
  - specialize (IHexec1 _ ltac:(eauto)); repeat deex.
    match goal with
    | [ H: result_rel sigma_rel  _ _ |- _ ] =>
      inversion H; subst; clear H
    end.
    specialize (IHexec2 _ ltac:(eauto)); repeat deex.
    simpl.
    exists r0; intuition eauto.
  - exists (Crashed sigma0); intuition eauto.
  - specialize (IHexec _ ltac:(eauto)); repeat deex.
    simpl.
    match goal with
    | [ H: result_rel sigma_rel  _ _ |- _ ] =>
      inversion H; subst; clear H
    end.
    exists (Crashed sigma2); intuition eauto.
  - specialize (IHexec _ ltac:(eauto)); repeat deex.
    simpl.
    match goal with
    | [ H: result_rel sigma_rel  _ _ |- _ ] =>
      inversion H; subst; clear H
    end.
    exists Failed; intuition eauto.
Qed.

Inductive rresult_rel Sigma1 Sigma2 (rel: Sigma1 -> Sigma2 -> Prop) T R :
  RResult Sigma1 T R -> RResult Sigma2 T R -> Prop :=
| RFinished_rel : forall sigma1 sigma2 v,
    rel sigma1 sigma2 ->
    rresult_rel rel (RFinished v sigma1) (RFinished v sigma2)
(* TODO: as above, add rresult_rel Finished Fail *)
| Recovered_rel : forall sigma1 sigma2 r,
    rel sigma1 sigma2 ->
    rresult_rel rel (Recovered r sigma1) (Recovered r sigma2)
| RFailed_rel : rresult_rel rel RFailed RFailed.

Hint Constructors rresult_rel.
Hint Constructors Prog.exec_recover.

Theorem translate_exec_recover : forall T R (p: seq_prog T) (rec: seq_prog R),
    forall ssigma sr,
      exec_recover p rec ssigma sr -> forall sigma,
        sigma_rel ssigma sigma ->
        (* NOTE: the equivalent recovery procedure is more generally run before
        [translate rec]. However, we need some way to handoff the recovered
        memory state to [fun v => translate (rec v)] while also making [rec] a
        complete program in [seq_prog]. *)
        exists r, Prog.exec_recover (translate p) (translate rec) sigma r /\
             rresult_rel sigma_rel sr r.
Proof.
  destruct 1; simpl; intros.
  - eapply translate_exec in H; eauto.
    repeat deex; eauto.
    match goal with
    | [ H: result_rel sigma_rel  _ _ |- _ ] =>
      inversion H; subst; clear H
    end.
    exists (RFinished v sigma2); intuition eauto.
  - eapply translate_exec in H; eauto.
    repeat deex; eauto.
    match goal with
    | [ H: result_rel sigma_rel  _ _ |- _ ] =>
      inversion H; subst; clear H
    end.
    exists (RFailed); intuition eauto.
  - dependent induction H0.
Abort.
