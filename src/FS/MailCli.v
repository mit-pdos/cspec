Require Import POCS.
Require Import MailServerImpl.
Require Import FSImpl.

Import ListNotations.
Require Import String.

Module mailserver := MailServer FS.

Axiom get_mail : proc string.

CoFixpoint loop u: proc unit :=
  m <- get_mail;
  _ <- mailserver.deliver u m;
  loop u.

Definition cli : proc unit :=
  init_ok <- mailserver.init;
  match init_ok with
  | Initialized =>
    u <- mailserver.newuser;
    loop u
  | InitFailed =>
    Ret tt
  end.

Extract Constant get_mail => "CLI.Stubs.getMail".
