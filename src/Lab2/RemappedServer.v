Require Import POCS.

Require Import RemappedDiskImpl.
Require Import BadSectorImpl.
Require Import Common.NbdServer.


Module d := RemappedDisk BadSectorDisk.
Module s := NBDServer d.

Definition serverLoop := s.serverLoop.
Definition diskSize := s.diskSize.
Definition init := s.init.
