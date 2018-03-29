Require Import POCS.
Require Import String.
Require Import MailServerAPI.
Require Import MailFSAPI.
Require Import MailFSStringAPI.
Require Import MailFSStringAbsAPI.


Module MailFSStringImpl' <:
  LayerImplMoversT
    MailFSStringAbsState
    MailFSStringOp MailFSStringAPI
    MailFSOp MailFSStringAbsAPI.
    
  Definition createwritetmp_core data :=
    tid <- Op (MailFSStringOp.GetTID);
    r <- Op (MailFSStringOp.CreateWriteTmp (encode_tid_fn tid 0) data);
    Ret r.

  Definition linkmail_core mboxfn :=
    tid <- Op (MailFSStringOp.GetTID);
    v <- Op (MailFSStringOp.LinkMail (encode_tid_fn tid 0) (encode_tid_fn tid mboxfn));
    Ret v.

  Definition unlinktmp_core :=
    tid <- Op (MailFSStringOp.GetTID);
    r <- Op (MailFSStringOp.UnlinkTmp (encode_tid_fn tid 0));
    Ret r.

  Definition list_core :=
    l <- Op (MailFSStringOp.List);
    Ret (map decode_tid_fn l).

  Definition compile_op T (op : MailFSOp.opT T) : proc MailFSStringOp.opT T :=
    match op with
    | MailFSOp.LinkMail m => linkmail_core m
    | MailFSOp.List => list_core
    | MailFSOp.Read fn => Op (MailFSStringOp.Read (encode_tid_fn (fst fn) (snd fn)))
    | MailFSOp.Delete fn => Op (MailFSStringOp.Delete (encode_tid_fn (fst fn) (snd fn)))
    | MailFSOp.CreateWriteTmp data => createwritetmp_core data
    | MailFSOp.UnlinkTmp => unlinktmp_core
    | MailFSOp.Ext extop => Op (MailFSStringOp.Ext extop)
    | MailFSOp.Lock => Op (MailFSStringOp.Lock)
    | MailFSOp.Unlock => Op (MailFSStringOp.Unlock)
    | MailFSOp.GetTID => Op (MailFSStringOp.GetTID)
    | MailFSOp.Random => Op (MailFSStringOp.Random)
    end.

  
  Theorem compile_op_no_atomics :
    forall `(op : _ T),
      no_atomics (compile_op op).
  Proof.
    destruct op; compute; eauto.
  Qed.

  
  Ltac step_inv :=
    match goal with
    | H : MailFSStringAbsAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    | H : MailFSStringAPI.step _ _ _ _ _ _ |- _ =>
      inversion H; clear H; subst; repeat sigT_eq
    end; intuition idtac.

  Hint Extern 1 (MailFSStringAbsAPI.step _ _ _ _ _ _) => econstructor.
  Hint Extern 1 (MailFSStringAPI.step _ _ _ _ _ _) => econstructor.

  Lemma gettid_right_mover :
    right_mover
      MailFSStringAPI.step
      (MailFSStringOp.GetTID).
  Proof.
    unfold right_mover; intros.
    repeat step_inv; eauto.

    eexists; split; econstructor.
  Qed.

  Hint Resolve gettid_right_mover.

  Theorem ysa_movers_linkmail_core: forall n,
    ysa_movers MailFSStringAPI.step (linkmail_core n).
  Proof.
    econstructor; eauto 20.
  Qed.

  Hint Resolve ysa_movers_linkmail_core.

  Theorem ysa_movers_list_core:
    ysa_movers MailFSStringAPI.step list_core.
  Proof.
    unfold list_core, ysa_movers.
    eauto 20.
  Qed.

  Hint Resolve ysa_movers_list_core.

  Theorem ysa_movers_createwritetmp_core: forall s,
    ysa_movers MailFSStringAPI.step (createwritetmp_core s).
  Proof.
    econstructor; eauto 20.
  Qed.

  Hint Resolve ysa_movers_createwritetmp_core.

  Theorem ysa_movers_unlinktmp_core:
    ysa_movers MailFSStringAPI.step unlinktmp_core.
  Proof.
    econstructor; eauto 20.
  Qed.

  Hint Resolve ysa_movers_unlinktmp_core.

  Theorem ysa_movers : forall `(op : _ T),
    ysa_movers MailFSStringAPI.step (compile_op op).
  Proof.
    destruct op; simpl; eauto 20.
  Qed.

  Theorem compile_correct :
    compile_correct compile_op MailFSStringAPI.step MailFSStringAbsAPI.step.
  Proof.
    unfold compile_correct; intros.
    destruct op.

    all: try solve [ repeat atomic_exec_inv; repeat step_inv; eauto ].

    repeat atomic_exec_inv.
    repeat step_inv; eauto.

    destruct fn; simpl in *.
    eauto.

    destruct fn; simpl in *.
    eauto.
  Qed.

End MailFSStringImpl'.

Module MailFSStringImpl :=
  LayerImplMovers
    MailFSStringAbsState
    MailFSStringOp MailFSStringAPI
    MailFSOp MailFSStringAbsAPI
    MailFSStringImpl'.

Module MailFSStringImplH' :=
  LayerImplMoversHT
    MailFSStringAbsState
    MailFSStringOp MailFSStringAPI
    MailFSOp MailFSStringAbsAPI
    MailFSStringImpl'
    UserIdx.

Module MailFSStringImplH :=
  LayerImplMovers
    MailFSStringAbsHState
    MailFSStringHOp MailFSStringHAPI
    MailFSHOp MailFSStringAbsHAPI
    MailFSStringImplH'.
