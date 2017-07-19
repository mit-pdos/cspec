Require Import POCS.
Require Extraction.

Extraction Language Haskell.

Extract Constant bytes => "BS.ByteString".
Extract Constant bytes_dec => "(\n b1 b2 -> b1 Prelude.== b2)".
Extract Constant bytes0 => "(\n -> BS.replicate (Prelude.fromIntegral n) 0)".

Extract Constant bappend => "(\_ _ bs1 bs2 -> BS.append bs1 bs2)".
Extract Constant bsplit => "(\n1 _ bs -> BS.splitAt (Prelude.fromIntegral n1) bs)".
