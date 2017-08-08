Require Import POCS.
Require Import NbdAPI.


Extraction Language Haskell.

Module NbdImpl <: NbdAPI.

  Axiom init: proc InitResult.
  Axiom getRequest : proc Request.
  Axiom sendResponse : Response -> proc unit.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom getRequest_ok : proc_spec (getRequest_spec) (getRequest) recover abstr.
  Axiom sendResponse_ok : forall resp, proc_spec (sendResponse_spec resp) (sendResponse resp) recover abstr.
  Axiom recover_noop : rec_noop recover abstr wipe_req.

End NbdImpl.

Extract Constant Handle => "Data.Word.Word64".
Extract Constant NbdImpl.getRequest => "Server.getRequestFromQueue".
Extract Constant NbdImpl.sendResponse => "Server.sendResponseOnQueue".
