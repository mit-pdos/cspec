# 6.826-labs
Labs for 6.826 (POCS)

## Hacking

```
make [-jN]
make -f Makefile.coq src/Shallow/ReplicatedDisk.vo
```

The Makefile generates a `_CoqProject` listing out the files in the project
using `git`, then `Makefile.coq`, and it calls that. The fact that files are
retrieved using `git` means you need to `git add` before a file will be built.

`make` also runs extraction by compiling `ExtractReplicatedDisk.v`. This process
is still a bit hacky - I'd like to fix it by determining some useful features
for Coq to have, implementing those, and getting them merged upstream.

## Running the replicated disk as an nbd server

The only tools you need are `stack` for building the server and `nbd-client` for
connecting to it. If you're not familiar
with [Stack](https://docs.haskellstack.org/en/stable/GUIDE/), it's a build tool
for Haskell aiming for reproducible, local builds. Using Stack, compiling will
fetch, build, and use stable versions of all dependencies (including GHC
itself), independent of the rest of your Haskell setup.

```
make
cd replicate-nbd
stack setup
stack build
```

TODO: what does `stack setup` do? Supposedly it downloads the compiler, but is
this necessary on a clean setup, or is `stack build` sufficient?

Once you've compiled, run the server:

```
stack exec replicate-nbd
```

The underlying disks will be `disk0.img` and `disk1.img` in the current
directory, which are initialized to two empty 100MB files if they don't exist.
This will eventually be customizable using options to `replicate-nbd`.

Connect to it from a client:

```
sudo nbd-client localhost /dev/nbd0
```

Note that you can use `nbd` over the network (this is what it's intended for). I
use this to run the server from my Mac but mount it in a Linux virtual machine,
by accessing the host machine over a VirtualBox NAT. I believe this just entails
setting your VM's Network Adapter's "Attached to:" setting to "NAT" and then
using 10.0.2.2 as the hostname for `nbd-client` rather than `localhost`.

Use it a bit (you can do this without sudo by adding yourself to the disk
group: `sudo usermod -a -G disk $USER`) (TODO: possibly Arch-specific):

```
mkfs.ext4 -E root_owner /dev/nbd0
sudo mkdir /mnt/nbd
sudo mount /dev/nbd0 /mnt/nbd
mkdir /mnt/nbd/dir
ls /mnt/nbd
sudo umount /mnt/nbd
```

Disconnect the block device:

```
sudo nbd-client -d /dev/nbd0
```

The server won't exit since it continually accepts new connections, but you can
send an interrupt signal with `Ctrl-C`.

# Reading guide

There are two distinct experiments, in the `Shallow` and `Refinement`
subdirectories.

* `Automation.v`: a bunch of nice Ltac
* `Bytes.v`: (currently axiomatic) definition of byte strings of known lengths.
* `ExtrBytes.v`: extraction of axiomatic `bytes` definitions to Haskell
  `Data.ByteString`.
* `SepLogic/`: (the start of) a separation logic library, somewhat modelled
  after FSCQ's separation logic but mostly influenced by FRAP. There is little
  automation so far as it has not yet been necessary.
  * `Mem/`: as in FSCQ, a `mem A V` is a `A -> option V`, where addresses are
    required to have deciable equality in order to update memories.
  * `Pred/`: predicates over memories, including separation logic connectives
    and primitives (`star`, `ptsto`, etc.)
* `Disk.v`: defines `disk`, a memory with fixed size that always maps addresses
  [0, size).
* `Shallow/`

  FSCQ-like programming languages at each layer. We have a generic `prog` and
  semantics, so that each layer specifies some operations and how they execute
  but gets the rest of the semantics for free.

  - `ProgLang/Prog.v`: programs over generic operations, parametrized by the operations'
    semantics.
  - `ProgLang/ProgTheorems.v`: some sample theorems about the execution semantics,
    including the monad laws
  - `ProgLang/Hoare.v`: Hoare quadruples and doubles, with desugaring
    from quadruples to doubles and some equivalence proofs between the different
    spec definitions.
  - `Interpret.v`: implementing one language (the "spec language") in terms of
    another (the "implementation language") by providing implementations for
    each spec operation and proving semantics preservation in a refinement-based
    approach. Produces a theorem about spec programs translated to
    implementation programs, including a hidden recovery procedure that is
    specific to the language implementation.
  - `TwoDiskProg.v`: instantiation of `prog` for programs that manipulate two
    disks, where one might fail at any time.
  - `SeqDiskProg.v`: programs over a single disk without failures.
  - `ReplicatedDisk.v`: implements the `SeqDiskProg` interface using
    `TwoDiskProg`, using replication to handle failure of a single disk
    seamlessly. Includes a recovery procedure to patch up any inconsistency
    created due to a crash in the middle of writing to the two disks.

* `Refinement/`
  * `Implements/` defines an IO monad and the notion of an implementation
    refining the opaque behavior of this monad. This is our definition of what a spec is and when a program meets its specification.
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
