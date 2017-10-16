Require Import POCS.

Import ListNotations.
Require Import String.
Require Import FS.SepLogic.Mem.
Require Import FS.SepLogic.Pred.
Require Import FS.FSAPI.


Definition message := string.

Definition mailbox := list message.

Definition user := string.

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

Definition delete_spec user m : Specification _ _ unit State :=
  fun '(F, mbox) state => {|
    pre :=
      state |= F * user |-> mbox;
    post := fun r state' =>
      r = tt /\
      state' |= F * user |-> filter (fun m' => if (string_dec m m') then true else false) mbox;
    recovered := fun _ _ => False
  |}.

Definition newuser_spec : Specification _ _ unit State :=
  fun F state => {|
    pre :=
      state |= F;
    post := fun r state' =>
      exists uid,
      r = uid /\
      state' |= F * uid |-> nil;
    recovered := fun _ _ => False
  |}.


Module Type MailServerAPI.

  Axiom init : proc InitResult.
  Axiom deliver : user -> message -> proc unit.
  Axiom read : user -> proc mailbox.
  Axiom delete : user -> string -> proc unit.
  Axiom newuser : proc user.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom deliver_ok : forall uid msg, proc_spec (deliver_spec uid msg) (deliver uid msg) recover abstr.
  Axiom read_ok : forall uid, proc_spec (read_spec uid) (read uid) recover abstr.
  Axiom delete_ok : forall uid i, proc_spec (delete_spec uid i) (delete uid i) recover abstr.
  Axiom newuser_ok : proc_spec newuser_spec newuser recover abstr.
  Axiom recover_noop : rec_noop recover abstr no_crash.

  Hint Resolve init_ok.
  Hint Resolve deliver_ok.
  Hint Resolve read_ok.
  Hint Resolve delete_ok.
  Hint Resolve newuser_ok.
  Hint Resolve recover_noop.

End MailServerAPI.
