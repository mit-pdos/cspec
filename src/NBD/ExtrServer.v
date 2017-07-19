Require Import Refinement.Prog.
Require Import NBD.NbdData.

Axiom getRequest : prog Request.
Axiom sendResponse : Response -> prog unit.

Extraction Language Haskell.

Extract Constant Handle => "Data.Word.Word64".
Extract Constant getRequest => "Server.getRequestFromQueue".
Extract Constant sendResponse => "Server.sendResponseOnQueue".
