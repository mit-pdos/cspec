Cd "mail-test/extract/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellString.

Extraction Language Haskell.

Require Import Mail2.MailServer.
Require Import Mail2.MailFSStringAbsAPI.

Extract Inlined Constant encode_tid_fn => "Support.encode_tid_fn".
Extract Inlined Constant decode_tid_fn => "Support.decode_tid_fn".

Separate Extraction ms_bottom.

Cd "../../".
