Require Import POCS.

Require Import ReplicatedDisk.ReplicatedDiskImpl.
Require Import TwoDisk.TwoDiskImpl.
Require Import TwoDisk.TwoDiskBaseImpl.
Require Import NBD.NbdServer.


Module td := TwoDisk TwoDiskBase.
Module rd := ReplicatedDisk td.
Module s := NBDServer rd.

Definition serverLoop := s.serverLoop.
Definition diskSize := s.diskSize.
Definition init := s.init.
