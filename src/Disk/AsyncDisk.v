Require Import Automation.

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
    (* the durable value could be current_val or one of the following *)
    durable_vals: list block; }.

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

Definition subset A (l l': list A) :=
  forall a, List.In a l -> List.In a l'.

Instance subset_preorder {A} : PreOrder (subset (A:=A)).
Proof.
  econstructor; hnf; intros.
  unfold subset; intros; eauto.
  unfold subset in *; eauto.
Qed.

Inductive pflush_blockhist: blockhist -> blockhist -> Prop :=
| pflush_blockhist_subset: forall h h',
    current_val h = current_val h' ->
    subset (durable_vals h') (durable_vals h) ->
    pflush_blockhist h h'.

Instance pflush_blockhist_preorder : PreOrder pflush_blockhist.
Proof.
  econstructor; hnf; intros.
  - econstructor; eauto.
    reflexivity.
  - inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    econstructor; eauto.
    congruence.
    etransitivity; eauto.
Qed.

Definition bufferHist (b:block) (h:blockhist) : blockhist :=
  {| current_val := b;
     durable_vals :=
       current_val h :: durable_vals h; |}.

Instance blockhist_async: AsyncBlock blockhist :=
  {| flushBlock := fun bs => {| current_val := current_val bs;
                             durable_vals := nil |};
     pflushBlock := pflush_blockhist;
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

Hint Rewrite curr_val_blockstate : block.
Hint Rewrite curr_val_blockhist : block.

Definition flush {B} {async:AsyncBlock B} (d:diskOf B) : diskOf B :=
  mapDisk d flushBlock.

Definition pflush {B} {async:AsyncBlock B} : diskOf B -> diskOf B -> Prop :=
  fun d d' => pointwise_rel pflushBlock d d'.

Instance pflush_preorder {B} {async:AsyncBlock B} : PreOrder (pflush (async:=async)).
Proof.
  unshelve eapply pointwise_rel_preorder.
  apply pflushBlock_preorder.
Qed.

Definition wipeDisk (d:disk) : disk :=
  mapDisk d wipeBlockstate.

Record collapsesTo (h:blockhist) (bs:blockstate) : Prop :=
  is_collapse
    { collapse_current: curr_val h = curr_val bs;
      collapse_durable: List.In (durable_val bs) (curr_val h::durable_vals h); }.

Definition covered (d:diskOf blockhist) (d':disk) :=
  pointwise_rel collapsesTo d d'.

Lemma collapsesTo_buffer : forall h bs b,
    collapsesTo h bs ->
    collapsesTo (buffer b h) (buffer b bs).
Proof.
  simpl; intros.
  destruct H.
  econstructor; eauto.
  simpl; intuition eauto.
Qed.

Global Opaque curr_val.
Global Opaque buffer.
