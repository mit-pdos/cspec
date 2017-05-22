List of high-level concepts to explain within and outside of code for students to understand the infrastructure and assignments.

# Coq

* Prop universe
* `Notation``
* notation scopes
* implicit arguments (`Set Implicit Arguments` and manually with `Arguments`)
* `Opaque`
* `Record` and builder notation
* `Coercion` and `:>` in record field
* `Implicit Type`
* `Hint Rewrite`
* Curry-Howard negation (`~`)
* `Axiom`
* inductive types, type parameters
* `Hint Constructors`
* `clos_refl_trans_1n`
* generalization with backquote
* `{T}` for implicit arguments
* "maximally inserted" implicit arguments (eg, `Ret`)
* `Section` and section variables
* destructuring let in binder ("pattern") (`fun '(a, b) =>`)
* partially applied `eq`

# Programming Languages

* "axiomatic"
* predicates
* "extensional" equality
* idea of `prog` being a model of programs
* semantics for an operation
* inductive predicates
* big-step vs small-step semantics
* monads (at least bind and ret combinators)
* induction over proofs
* "equivalence" (esp notion of program equivalence, exec respects program equivalence)
* inversion (as in inversion lemmas)
* "desugar"
* spec weakening
* idempotent (in the sense used in FSCQ)
* composition
* refinement (invariants, abstraction functions)
* abstract state
* ghost state
* "parametrized over"
