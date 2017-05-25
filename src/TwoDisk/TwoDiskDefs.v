Require Export Disk.

Inductive diskId := d0 | d1.

Inductive DiskResult T :=
| Working (v:T)
| Failed.

Arguments Failed {T}.
