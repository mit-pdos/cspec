Require Import POCS.

Require Import RemappedDisk.RemappedDiskImpl.
Require Import BadSectorDisk.BadSectorImpl.
Require Import NBD.NbdServer.


Module d := RemappedDisk BadSectorDisk.
Module s := NBDServer d.

Definition serverLoop := s.serverLoop.
Definition diskSize := s.diskSize.
Definition init := s.init.
