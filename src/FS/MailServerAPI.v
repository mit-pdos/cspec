Require Import POCS.


Import ListNotations.
Require Import String.
Require Import FS.SepLogic.Mem.
Require Import FS.SepLogic.Pred.
Require Import FS.FSAPI.


Record message := mk_message {
  MessageData : list nat;
}.

Definition mailbox := list message.

Definition user := nat.

Definition State := mem user mailbox.


Definition inited (s : State) : Prop :=
  s = empty_mem.


Definition deliver_spec user message : Specification _ _ unit State :=
  fun '(F, mbox) state => {|
    pre :=
      state |= F * user |-> mbox;
    post := fun r state' =>
      r = tt /\
      state |= F * user |-> (mbox ++ [message]);
    recovered := fun _ _ => False
  |}.

Definition read_spec user : Specification _ _ unit State :=
  fun '(F, mbox) state => {|
    pre :=
      state |= F * user |-> mbox;
    post := fun r state' =>
      r = mbox /\
      state' |= F * user |-> mbox;
    recovered := fun _ _ => False
  |}.

Definition delete_spec user idx : Specification _ _ unit State :=
  fun '(F, mbox) state => {|
    pre :=
      state |= F * user |-> mbox;
    post := fun r state' =>
      r = tt /\
      state' |= F * user |-> (firstn idx mbox ++ (skipn (S idx) mbox));
    recovered := fun _ _ => False
  |}.


Module Type MailServerAPI.

  Axiom init : proc InitResult.
  Axiom deliver : user -> message -> proc unit.
  Axiom read : user -> proc mailbox.
  Axiom delete : user -> nat -> proc unit.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom deliver_ok : forall uid msg, proc_spec (deliver_spec uid msg) (deliver uid msg) recover abstr.
  Axiom read_ok : forall uid, proc_spec (read_spec uid) (read uid) recover abstr.
  Axiom delete_ok : forall uid i, proc_spec (delete_spec uid i) (delete uid i) recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_crash.

  Hint Resolve init_ok.
  Hint Resolve deliver_ok.
  Hint Resolve read_ok.
  Hint Resolve delete_ok.
  Hint Resolve recover_noop.

End MailServerAPI.
