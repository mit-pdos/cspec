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

Hint Constructors result_rel.
Hint Constructors Prog.exec.

Ltac prog_bind :=
  eapply Prog.ExecBindFinished.
Ltac prog_step :=
  first [ eapply Prog.ExecStepTo ||
                 eapply Prog.ExecStepFail ];
  simpl; simpl_match; eauto.

Ltac simp_stepto :=
  match goal with
  | [ H: rstep _ _ = StepTo _ _ |- _ ] =>
    progress cbn [rstep] in H;
    destruct_nongoal_matches;
    inversion H; subst; clear H
  end.

Theorem translate_exec : forall T (p: seq_prog T),
    forall sigma r,
      Prog.exec (translate p) sigma r ->
      forall ssigma, sigma_rel ssigma sigma ->
                exists sr, exec p ssigma sr /\
                      result_rel sigma_rel sr r.
Proof.
  induction p; simpl; intros.
Admitted.

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
Hint Constructors exec_recover.

Ltac inv_rel :=
  match goal with
  | [ H: result_rel _ _ _ |- _ ] =>
    inversion H; subst; clear H
  end.

Lemma RExecCrash_eq : forall T R (p: seq_prog T) (rec: seq_prog R)
                        sigma sigma' r r',
    exec p sigma (Crashed sigma') ->
    exec_recover rec rec sigma' r ->
    r' = to_recovered r ->
    exec_recover p rec sigma r'.
Proof.
  intros; subst.
  eauto.
Qed.

Hint Resolve RExecCrash_eq.

Ltac apply_translate :=
match goal with
      | [ H: Prog.exec (translate _) ?s _,
             H': sigma_rel _ ?s |- _ ] =>
        eapply translate_exec in H; eauto;
          repeat deex; repeat inv_rel
      end.

Lemma to_recovered_idempotent : forall T R Sigma (r: RResult Sigma R R),
    to_recovered (T:=T) (to_recovered (T:=R) r) = to_recovered r.
Proof.
  destruct r; simpl; eauto.
Qed.

Theorem translate_exec_self_recover : forall R (rec: seq_prog R),
    forall sigma r,
      Prog.exec_recover (translate rec) (translate rec) sigma r ->
      forall ssigma, sigma_rel ssigma sigma ->
                exists sr, exec_recover rec rec ssigma sr /\
                      rresult_rel sigma_rel sr r.
Proof.
  intros.
  generalize dependent ssigma.
  dependent induction H; simpl; intros;
    apply_translate.
  - exists (RFinished v sigma1); intuition eauto.
  - exists (RFailed); intuition eauto.
  - specialize (IHexec_recover rec r0).
    repeat match type of IHexec_recover with
           | ?P -> _ =>
             lazymatch type of P with
             | Prop => specialize (IHexec_recover ltac:(auto))
             | _ => idtac
             end
           end.
    admit. (* this seems to require some idempotence of the seq_prog recovery
    procedure - surprising, but maybe it's required? *)
Admitted.

Lemma rresult_rel_recovered : forall Sigma1 Sigma2 rel T R
                                (r: RResult Sigma1 R R)
                                (r': RResult Sigma2 R R),
    rresult_rel rel r r' ->
    rresult_rel (T:=T) rel (to_recovered r) (to_recovered r').
Proof.
  intros.
  inversion H; subst; simpl; eauto.
Qed.

Hint Resolve rresult_rel_recovered.

Theorem translate_exec_recover : forall T R (p: seq_prog T) (rec: seq_prog R),
    forall sigma r,
      (* NOTE: the equivalent recovery procedure is more generally run before
      [translate rec]. However, we need some way to handoff the recovered memory
      state to [fun v => translate (rec v)] while also making [rec] a complete
      program in [seq_prog]. *)
      Prog.exec_recover (translate p) (translate rec) sigma r ->
      forall ssigma, sigma_rel ssigma sigma ->
                exists sr, exec_recover p rec ssigma sr /\
                      rresult_rel sigma_rel sr r.
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
