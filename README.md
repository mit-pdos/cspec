# 6.826-labs
Labs for 6.826 (POCS)

## Hacking

`update-coqproject.sh` populates `_CoqProject` with files known to git. After
`git add NewFile.v`, re-run the script and commit the new `_CoqProject`.

`make` generates `Makefile.coq` and then compiles the default rule, which
compiles all the `.vo` files. `make -jN` will work correctly (`make` natively
handles parallelism across sub-makes correctly). To compile a specific file
you'll need to use `make -f Makefile.coq`.

`make clean` calls out to `Makefile.coq`'s clean rule.

## Reading guide

There are two distinct experiments, in the `Shallow` and `Refinement`
subdirectories.

* `Automation.v`: a bunch of nice Ltac
* `Bytes.v`: (currently axiomatic) definition of byte strings of known lengths.
  These will nicely extract to Haskell's `Data.ByteString.Strict`.
* `Mem.v`: as in FSCQ, a `mem A V` is a `A -> option V`, where addresses are
  required to have deciable equality in order to update memories.
* `Shallow`

  FSCQ-like programming languages at each layer. We avoid abstraction and thus
  repeat the definitions of `prog`, `exec`, and `exec_recover` at every layer.

  - `Prog.v`: programs over three disks (`prog3 T`).
  - `ProgTheorems.v`: some sample theorems about the execution semantics,
    including the monad laws
  - `Hoare.v`: (currently unused) Hoare quadruples and doubles, with desugaring
    from quadruples to doubles and some equivalence proofs between the different
    spec definitions.
  - `SequentialDisk.v`: programs over a single, sequential disk (`sprog T`).
  - `ReplicatedDisk.v`: implements each operation in `sprog` with a program in
    `prog3`, defines a simple translation/interpreter from `sprog` to `prog3`
    that uses these operations, and then proves that the translated code
    faithfully simulates the original. Follows much of the same approach as the
    optimistic translator in CFSCQ.

* `Refinement`
  - `IOstep.v`: assumes some operations in an `IO` monad, ncluding `Ret` and
    `Bind` operations, as well as its semantics. These programs have an opaque
    semantics: they manipulate state of type `world` according to some (unknown)
    relation `io_step`. We can add axioms for operations in `IO` and assume
    the appropriate `io_step` for these operations; `TwoDiskImpl` does so.

    For extraction `IO` is particularly clean: it just extracts to the Haskell
    `IO` monad! The assumed `Ret` and `Bind` because `return` and `(>>=)`, while
    the semantics and `world` state type are not needed for extraction. Then any
    axiomatized operations are provided as ordinary Haskell programs.
  - `IOcrash.v`: extends `IOstep` to also define `io_crash`, which is like step
    but has rules for crashing before a program starts, in the middle of a bind,
    and during either side of a bind.
  - `IO.v`: re-exports `IOstep` and `IOcrash` to give a complete semantics to
    the `IO` monad.
  - `Implements.v`: defines an `implements` relation between two relations based
    on refinement, linked via an abstraction function. A proof of an
    `implements` relation is a correctness specification.
  - `Disk.v`: self-explanatory; just defines `disk` as an appropriate memory,
    using `nat` addresses and 4KB values.
  - `TwoDiskAPI.v`: provides definitions for what operations on two disks should
    do; not quite an API since the signatures for `Read` and `Write` are not
    really given, but are instead implicit in the signatures for `Read` and
    `Write`'s semantics.

    We start using modules here for namespacing (there will be many things
    called `Read` and `Write`), but do not use module types or functors.
  - `TwoDiskImpl.v`: here are the actual operations for operating on two disks.
    Since this is the lowest level we don't actually provide implementations but
    just a set of axioms. Here we also provide `Read_ok` and `Write_ok` proofs
    that link the specs (in `TwoDiskAPI`) to the IO monad; these are also
    assumed, and give `TD.Read` and `TD.Write` meaning via refinement.
  - `SeqDiskAPI.v`: in analogy to `TwoDiskAPI.v`, provides the API (specs) for a
    single, sequential disk's operations.
  - `SeqDiskImpl.v`: implements the sequential disk operations using the
    two-disk operations. The implementation is kind of pointless without crashes
    (and really just uses the first disk), but the refinement proof already has
    some interesting issues. For example, it maintains an invariant that both
    disks have the same domain.
