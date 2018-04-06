Cd "mail-test/extract/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellString.

Extraction Language Haskell.

Require Import Mail2.MailServer.
Require Import Mail2.MailFSStringAbsAPI.
Require Import Mail2.MailServerAPI.

Extract Inlined Constant encode_tid_fn => "Support.encode_tid_fn".
Extract Inlined Constant decode_tid_fn => "Support.decode_tid_fn".
Extract Inlined Constant smtpconn => "Support.SMTPConn".
Extract Inlined Constant pop3conn => "Support.POP3Conn".

Separate Extraction ms_bottom ms_bottom_server ms_bottom_opt.

Cd "../../".
