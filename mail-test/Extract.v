Cd "mail-test/extract/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.

Extraction Language Haskell.

Require Import Mail2.MailServer.
Require Import Mail2.MailFSStringAbsAPI.
Require Import Mail2.MailServerAPI.

Extract Inlined Constant encode_tid_fn => "Support.encode_tid_fn".
Extract Inlined Constant decode_tid_fn => "Support.decode_tid_fn".
Extract Inlined Constant smtpconn => "Support.SMTPConn".
Extract Inlined Constant pop3conn => "Support.POP3Conn".

Extract Inlined Constant string => "Prelude.String".
Extract Inlined Constant string_length => "(\s -> Prelude.fromIntegral (Prelude.length s))".
Extract Inlined Constant tmp_string => """tmp""".
Extract Inlined Constant mail_string => """mail""".
Extract Inlined Constant bench_msg => """Hello world.""".

Separate Extraction ms_bottom ms_bottom_server.

Cd "../../".
