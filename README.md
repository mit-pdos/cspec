# deepspec-labs
Exercises for DSSS refinement/crashes

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
