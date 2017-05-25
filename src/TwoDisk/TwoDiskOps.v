Require Import TwoDisk.TwoDiskDefs.

Require Import Refinement.ProgLang.Prog.

Axiom read : diskId -> addr -> prog (DiskResult block).
Axiom write : diskId -> addr -> block -> prog (DiskResult unit).
Axiom diskSize : diskId -> prog (DiskResult nat).
