Require Export Bytes.

Extraction Language Haskell.

Extract Constant bytes => "BS.ByteString".
Extract Constant bytes_dec => "(\n b1 b2 -> b1 Prelude.== b2)".
Extract Constant bytes0 => "(\n -> BS.replicate (Prelude.fromIntegral n) 0)".
