Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.

Extraction Language Haskell.

Require Import Mail.MailServer.
Require Import Mail.MailFSStringAbsAPI.
Require Import Mail.MailServerAPI.

Extract Inlined Constant encode_tid_fn => "Support.encode_tid_fn".
Extract Inlined Constant decode_tid_fn => "Support.decode_tid_fn".
Extract Inlined Constant smtpconn => "Support.SMTPConn".
Extract Inlined Constant pop3conn => "Support.POP3Conn".

Extract Inlined Constant abstract_string => "BS.ByteString".
Extract Inlined Constant abstract_string_length => "(\s -> Prelude.fromIntegral (BS.length s))".
Extract Inlined Constant tmp_string => """tmp""".
Extract Inlined Constant mail_string => """mail""".
Extract Inlined Constant bench_msg => """Hello world.""".

Cd "mail-test/extract/".
Separate Extraction ms_bottom ms_bottom_server.
Cd "../../".
