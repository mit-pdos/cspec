Cd "mail-test/extract/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.

Extraction Language Haskell.

Require Import Mail2.MailServer.

Separate Extraction ms_bottom.

Cd "../../".
