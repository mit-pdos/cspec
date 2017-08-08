# 6.826-labs
Labs for 6.826 (POCS)

## TODO

### Experiment with transition systems

I believe that we can make the analogy to transition systems more clear
than it currently is. There are several changes that would go into
improving this connection:

- Make the state of the system include the program (note that the type
of states would be parametrized by the return type). A small step can
peel off one bind, or switch to recovery. Executing means turning the
program into a `Ret`. Note that we still need to record whether we're
in recovery, since the type of the program will change to `proc unit`
(at this point we can build this into the framework).

- Now a program is really synonymous with a transition system: just
consider starting states that have that program. Currently we have
something close with `exec p`, but folding the program into the state
makes the state uniform (the type of the transition relation is actually
`Relation (State T)`).

- Bring back explicit programming languages. "All programs" is no
longer about all contexts, but instead it's a representation of all
initial states, so it's a more natural idea. This is a clean solution.

- Programs are a special case of a transition system (notably, the states
are unusual in that they inform the transition relation greatly, as they
have code in them). However, we can define refinement without reference to
programs. Nonetheless Hoare-style specs are a great way to describe the
transition relation identified with a program (including the recovery
transitions). In theory we can do an example of a refinement between
two transition systems whose rules are coded up completely manually.

## Hacking

```
make [-jN]
make -f Makefile.coq src/SeqDisk/ReplicatedDisk.vo
```

The Makefile generates a `_CoqProject` listing out the files in the project
using `git`, then `Makefile.coq`, and it calls that. The fact that files are
retrieved using `git` means you need to `git add` before a file will be built.

`make` also runs extraction by compiling `ExtractReplicatedDisk.v`. This process
is still a bit hacky - I'd like to fix it by determining some useful features
for Coq to have, implementing those, and getting them merged upstream.

## Running the Haskell nbd server

See the [replicate-nbd README](replicate-nbd/README.md).

# Reading guide

Note that this guide has not been updated to reflect the addition of asynchronous disk replication.

* [Automation.v](src/Automation.v): a bunch of nice Ltac
* [Bytes.v](src/Bytes.v): (currently axiomatic) definition of byte strings of known lengths.
* [ExtrBytes.v](src/ExtrBytes.v): extraction of axiomatic `bytes` definitions to Haskell
  `Data.ByteString`.
* [SepLogic](src/SepLogic/): (the start of) a separation logic library, somewhat modelled
  after FSCQ's separation logic but mostly influenced by FRAP. There is little
  automation so far as it has not yet been necessary.
  * [Mem/](src/SepLogic/Mem/): as in FSCQ, a `mem A V` is a `A -> option V`, where addresses are
    required to have deciable equality in order to update memories.
  * [Pred/](src/SepLogic/Pred/): predicates over memories, including separation logic connectives
    and primitives (`star`, `ptsto`, etc.)
* [MaybeHolds](src/MaybeHolds.v): some simple infrastructure for conveniently stating properties of an `option` value. The core definition is `m |= F` (notation for `maybe_holds F m`, but you can read it as "m satisfies F"), which states that if `m` holds a value `x`, then `F(x)` is true.
* [Disk.v](src/Disk.v): defines `disk`, a memory with fixed size that always maps addresses
  [0, size).
* [Refinement/](src/Refinement/)

  We define an axiomatic `proc` inductive for programs. These programs have
  entirely opaque behavior, manipulating states of an axiom type `world`.
  Everything is built up in terms of _refinement_. The bottom-most level of the
  refinement goes from the two disk API to the `world` states, which we define
  in Haskell and assume has the appropriate refinement specification.

  - [ProgLang/Prog.v](src/Refinement/ProgLang/Prog.v): axiomatically defined programs. `proc` provides `Bind`
    and `Ret` combinators to build up programs, but other operations available
    are opaque.
  - [ProgLang/ProgTheorems.v](src/Refinement/ProgLang/ProgTheorems.v): some basic theorems about the execution
    semantics, including the monad laws
  - [ProgLang/Hoare.v](src/Refinement/ProgLang/Hoare.v): Hoare quadruples and theorems to chain specifications (including chaining recovery procedures).
  - [Interface.v](src/Refinement/Interface.v): Layer of operations, with their implementations and
    refinement proofs.
* [TwoDisk/](src/TwoDisk/) Programs that manipulate two disks, one of which may fail at any time.
  - [TwoDiskAPI.v](src/TwoDisk/TwoDiskAPI.v): Layer API, giving the operations and their semantics.
  - [TwoDiskImpl.v](src/TwoDisk/TwoDiskImpl.v): construction of an interface for two disk programs, using axioms for the operations and correctness proofs. This layer is implemented in Haskell by supplying regular Haskell functions at extraction time.
* [SeqDisk/](src/SeqDisk/): Programs that manipulate a single, synchronous disk, without failures.
  - [SeqDiskAPI.v](src/SeqDisk/SeqDiskAPI.v): Layer API.
  - [ReplicatedDisk.v](src/SeqDisk/ReplicatedDisk.v): implements the `SeqDiskAPI` interface using an implementation of `TwoDiskAPI`, using replication to handle failure of a single disk seamlessly. Includes a recovery procedure to patch up any inconsistency created due to a crash in the middle of writing to the two disks.
