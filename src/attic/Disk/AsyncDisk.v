Require Import Automation.
Require Import Pocs.Ensemble.

Require Export Disk.GenericDisk.

(* we only import List for the [In] predicate *)
Require List.
Require Import Sized.

(* TODO: document these definitions *)

Record blockstate :=
  { cache_val: option block;
    durable_val: block; }.

Definition disk := diskOf blockstate.

Record blockhist :=
  { current_val: block;
    durable_vals: Ensemble block;
    durable_includes_current: In current_val durable_vals; }.

(* a spec-only disk giving the possible durable states of each address *)
Definition histdisk := diskOf blockhist.

Class AsyncBlock B :=
  { flushBlock: B -> B;
    pflushBlock: B -> B -> Prop;
    pflushBlock_preorder: PreOrder pflushBlock;
    buffer: block -> B -> B;
    curr_val: B -> block; }.

Definition wipeBlockstate (bs: blockstate) : blockstate :=
  {| cache_val := None;
     durable_val := durable_val bs; |}.

Inductive pflush_blockstate: blockstate -> blockstate -> Prop :=
| pflush_blockstate_id: forall bs,
    pflush_blockstate bs bs
| pflush_blockstate_flush: forall bs b,
    cache_val bs = Some b ->
    pflush_blockstate bs {| cache_val := None;
                            durable_val := b |}.

Instance pflush_blockstate_preorder : PreOrder pflush_blockstate.
Proof.
  econstructor; hnf; intros.
  - constructor.
  - inversion H; subst; clear H; auto.
    inversion H0; subst; clear H0; auto.
    econstructor; eauto.
    simpl in *.
    congruence.
Qed.

Instance blockstate_async: AsyncBlock blockstate :=
  {| flushBlock := fun bs => match cache_val bs with
                          | Some b => {| cache_val := None;
                                        durable_val := b |}
                          | None => bs
                          end;
     pflushBlock := pflush_blockstate;
     buffer := fun b bs => {| cache_val := Some b;
                           durable_val := durable_val bs; |};
     curr_val := fun bs => match cache_val bs with
                        | Some b => b
                        | None => durable_val bs
                        end;
  |}.

Definition bufferHist (b:block) (h:blockhist) : blockhist :=
  {| current_val := b;
     durable_vals :=
       Add b (durable_vals h);
     durable_includes_current := ltac:(eauto); |}.

Inductive wipeBlockhist : blockhist -> blockhist -> Prop :=
| histcrash_to_hist_block : forall h b pf,
    In b (durable_vals h) ->
    wipeBlockhist h {| current_val := b;
                       durable_vals := Singleton b;
                       durable_includes_current := pf; |}.

Instance blockhist_async: AsyncBlock blockhist :=
  {| flushBlock := fun bs => {| current_val := current_val bs;
                             durable_vals := Singleton (current_val bs);
                             durable_includes_current := ltac:(auto); |};
     pflushBlock := eq;
     buffer := bufferHist;
     curr_val := current_val; |}.

Theorem curr_val_blockstate : forall c p,
    curr_val {| cache_val := c;
                durable_val := p |} =
    match c with
    | Some b => b
    | None => p
    end.
Proof.
  auto.
Qed.

Theorem curr_val_some_cache : forall b (bs: blockstate),
    cache_val bs = Some b ->
    curr_val bs = b.
Proof.
  simpl; intros; simpl_match; auto.
Qed.

Theorem curr_val_blockhist : forall (h: blockhist),
    curr_val h = current_val h.
Proof.
  auto.
Qed.

Theorem curr_val_buffer_blockstate : forall (bs: blockstate) b,
    curr_val (buffer b bs) = b.
Proof.
  auto.
Qed.

Theorem curr_val_buffer_blockhist : forall (bs: blockhist) b,
    curr_val (buffer b bs) = b.
Proof.
  auto.
Qed.

Theorem durable_val_buffer : forall (bs: blockhist) b,
    durable_vals (buffer b bs) = Add b (durable_vals bs).
Proof.
  auto.
Qed.

Hint Rewrite curr_val_blockstate : block.
Hint Rewrite curr_val_blockhist : block.
Hint Rewrite curr_val_buffer_blockhist : block.
Hint Rewrite curr_val_buffer_blockstate : block.
Hint Rewrite durable_val_buffer : block.

Global Opaque curr_val.
Global Opaque buffer.

Definition flush {B} {async:AsyncBlock B} : diskOf B -> diskOf B :=
  mapDisk flushBlock.

Definition pflush {B} {async:AsyncBlock B} : diskOf B -> diskOf B -> Prop :=
   pointwise_rel pflushBlock.

Instance pflush_preorder {B} {async:AsyncBlock B} : PreOrder (pflush (async:=async)).
Proof.
  unshelve eapply pointwise_rel_preorder.
  apply pflushBlock_preorder.
Qed.

Definition wipeDisk : disk -> disk :=
  mapDisk wipeBlockstate.

Definition wipeHist : histdisk -> histdisk -> Prop :=
  pointwise_rel wipeBlockhist.

Hint Unfold wipeHist : disk.

Record collapsesTo (h:blockhist) (bs:blockstate) : Prop :=
  is_collapse
    { collapse_current: curr_val h = curr_val bs;
      collapse_durable: In (durable_val bs) (durable_vals h); }.

Definition covered (d:histdisk) (d':disk) :=
  pointwise_rel collapsesTo d d'.

Hint Unfold pflush wipeDisk covered : disk.

Theorem collapsesTo_buffer : forall h bs b,
    collapsesTo h bs ->
    collapsesTo (buffer b h) (buffer b bs).
Proof.
  simpl; intros.
  destruct H.
  econstructor; simpl; eauto.
  autorewrite with block.
  eauto.
Qed.

Inductive histcrash : blockhist -> blockstate -> Prop :=
| histcrash_block : forall h b,
    In b (durable_vals h) ->
    histcrash h {| cache_val := None;
                   durable_val := b; |}.

Local Hint Constructors histcrash.

Definition crashesTo : histdisk -> disk -> Prop :=
  pointwise_rel histcrash.

Hint Unfold crashesTo : disk.

(* Special properties after flushing. *)

Definition block_flushed (bs:blockstate) : Prop :=
  cache_val bs = None.

Definition disk_flushed : disk -> Prop :=
  pointwise_prop block_flushed.

Theorem flush_flushed : forall (d:disk),
    disk_flushed (flush d).
Proof.
  intros.
  econstructor; simpl; intros.
  destruct matches.
  unfold block_flushed; simpl; auto.
Qed.

Theorem wipe_flushed : forall (d:disk),
    disk_flushed (wipeDisk d).
Proof.
  intros.
  econstructor; simpl; intros.
  destruct matches.
  unfold block_flushed; simpl; auto.
Qed.

Theorem histcrash_block_flushed : forall h bs,
    histcrash h bs ->
    block_flushed bs.
Proof.
  intros.
  inversion H; subst.
  econstructor; eauto.
Qed.

Theorem crash_flushed : forall d d',
    crashesTo d d' ->
    disk_flushed d'.
Proof.
  intros.
  econstructor; simpl; intros.
  eapply pointwise_rel_holds with (a:=a) in H.
  destruct matches in *;
    try contradiction;
    eauto using histcrash_block_flushed.
Qed.

Hint Resolve flush_flushed wipe_flushed crash_flushed.

Theorem flushed_pflush : forall (d d':disk),
    disk_flushed d ->
    pflush d d' ->
    d' = d.
Proof.
  intros.
  eapply diskMem_ext_eq.
  extensionality a.
  apply pointwise_prop_holds with (a:=a) in H.
  apply pointwise_rel_holds with (a:=a) in H0.
  unfold disk_get in *.
  destruct matches in *; try contradiction.
  inversion H0; subst; try congruence.
Qed.

Theorem flushed_flush : forall (d:disk),
    disk_flushed d ->
    flush d = d.
Proof.
  intros.
  eapply diskMem_ext_eq.
  extensionality a.
  simpl.
  apply pointwise_prop_holds with (a:=a) in H.
  unfold disk_get in *.
  destruct matches in *; try contradiction.
Qed.

Theorem flushed_crash : forall (d:disk),
    disk_flushed d ->
    wipeDisk d = d.
Proof.
  intros.
  eapply diskMem_ext_eq.
  extensionality a.
  simpl.
  apply pointwise_prop_holds with (a:=a) in H.
  unfold disk_get in *.
  destruct matches in *; try contradiction.
  unfold block_flushed, wipeBlockstate in *.
  destruct b; simpl in *; subst; auto.
Qed.

Hint Rewrite flushed_flush flushed_crash
     using (solve [ eauto ]) : flush.

Definition hist_flushed (h:blockhist) : Prop :=
  durable_vals h = Singleton (curr_val h).

Definition histdisk_flushed : histdisk -> Prop :=
  pointwise_prop hist_flushed.

Theorem wipeBlockhist_eq : forall h h',
    In (curr_val h') (durable_vals h) ->
    hist_flushed h' ->
    wipeBlockhist h h'.
Proof.
  intros.
  inversion H0.
  destruct h'; simpl in *.
  generalize durable_includes_current0.
  rewrite H2; autorewrite with block; simpl.
  intros.
  econstructor; eauto.
Qed.

Theorem histdisk_flush_is_flushed : forall d,
    histdisk_flushed (flush d).
Proof.
  intros.
  econstructor; intros; simpl.
  destruct matches.
  econstructor.
Qed.

Theorem histdisk_flushed_flush : forall d,
    histdisk_flushed d ->
    flush d = d.
Proof.
  intros.
  eapply diskMem_ext_eq.
  extensionality a; simpl.
  apply pointwise_prop_holds with (a:=a) in H.
  unfold disk_get in *.
  destruct matches.
  f_equal.
  destruct b.
  inversion H; simpl in *.
  autorewrite with block in *; simpl in *.
  subst.
  f_equal.
  apply ProofIrrelevance.proof_irrelevance.
Qed.

Theorem wipeBlockhist_hist_flushed : forall h h',
    wipeBlockhist h h' ->
    hist_flushed h'.
Proof.
  intros.
  inversion H; subst.
  econstructor; eauto.
Qed.

Hint Resolve wipeBlockhist_hist_flushed.

Theorem wipeHist_flushed : forall d d',
    wipeHist d d' ->
    histdisk_flushed d'.
Proof.
  intros.
  destruct H.
  econstructor; intros.
  specialize (pointwise_rel_holds a).
  destruct matches in *; try contradiction; eauto.
Qed.

Hint Resolve histdisk_flush_is_flushed.
Hint Resolve wipeHist_flushed.

(** * predicate transformers *)

Definition then_wipe (F: disk -> Prop) : disk -> Prop :=
  fun d' => exists d, F d /\ d' = wipeDisk d.

Theorem collapsesTo_wipe : forall h bs,
    collapsesTo h bs ->
    histcrash h (wipeBlockstate bs).
Proof.
  inversion 1; intros.
  econstructor; eauto.
Qed.

Theorem then_wipe_covered : forall d d',
    then_wipe (covered d) d' ->
    crashesTo d d'.
Proof.
  unfold then_wipe; intros; deex.
  autounfold with disk in *.
  pointwise; simpl in *; destruct matches in *.
  inversion Heqo0; subst.
  eauto using collapsesTo_wipe.
Qed.

Definition then_flush (F: disk -> Prop) : disk -> Prop :=
  fun d' => exists d, F d /\ d' = flush d.

Theorem then_flush_flushed : forall F d,
    then_flush F d ->
    disk_flushed d.
Proof.
  unfold then_flush; intros; deex; auto.
Qed.

Hint Resolve then_flush_flushed.
