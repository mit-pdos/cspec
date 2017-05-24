Require Import NBD.NbdData.
Require Import NBD.Server.

Extraction Language Haskell.

Extract Constant Handle => "Data.Word.Word64".
Extract Constant getRequest => "Server.getRequestFromQueue".
Extract Constant sendResponse => "Server.sendResponseOnQueue".
