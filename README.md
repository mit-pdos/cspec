# deepspec-labs
Exercises for DSSS refinement/crashes

## Preface

Please do not post public copies of this repository (e.g., by making
a public copy of it in your Github account) or post your solutions.
We plan to use this material for a class at MIT this coming fall semester.

## Exercise 1: implement and prove StatDB's implementation of Mean.

The current StatDB code does not properly implement the `mean` function.
If you run statdb-cli, you will see that it always returns 0:

```
% make bin/statdb-cli
...
% ./bin/statdb-cli
Mean: Just 0
Enter a number to add: 5
Mean: Just 0
Enter a number to add: 1
Mean: Just 0
Enter a number to add: 0
Mean: Just 0
...
```

Your job is to implement the `mean` function in `src/StatDb/StatDbImpl.v`,
and to prove that it is correct, by fixing up the proof at the bottom of
that same file.

## Exercise 2: bad sector remapping.

`src/RemappedDisk` contains a partial implementation of bad-sector
remapping.  The idea is to take a disk that has a bad sector, and make
it look like a fully working disk by remapping the bad sector to another
sector (the last sector).  For simplicity, we assume there is exactly
one bad sector.

We provide an implementation of `read` in `src/RemappedDisk/RemappedDiskImpl.v`.
Your job is to fill in several other parts of that file:

- Implement `write`.

- Fill in the abstraction relation `remapped_abstraction`.

- Finish the proof at the bottom of the file, which includes (1) fixing
  up the proof of the existing `read` implementation based on your
  abstraction, (2) proving your `write` implementation with your abstraction,
  and (3) proving that the existing `init` implementation establishes
  your abstraction in the initial state.
  
## Exercise 3: replicated disk without recovery

`src/ReplicatedDisk` contains a partial implementation of a replicated disk.
remapping.  The idea is to use two physical disks so that if one fails, the
application can continue with the remaining one.  If a fails and is replaced
with a new one, the implementation should fix up the new disk to reflect all the
writes the non-failed disk has seen.  We assume that both disks won't fail at
the same time.

We provide an implementation of `read` in `src/ReplicatedDisk/ReplicatedDiskImpl.v`.
Your job is to fill in several other parts of that file:

- Implement `write`.

- Complete the spec for `write_ok` and prove it.  Using the `step` ltac this
  proof is straightforward.

- To get some confidence that your `write_ok` spec is correct, also prove
  `write_read_check_ok`, which verifies that a read after a write observes the
  effect of the write.  Using the `step` ltac this proof is straightforward.

- Complete the spec for `init_ok` and prove it. This is a bit challenging since
  `Init` calls `init_at` to initialize each block recursively.  So, you will
  also have to write the spec for and prove `init_at_ok`. Your proof of `init_at_ok`
  will use induction.


## Exercise 4: replicated disk with recovery

TBD
