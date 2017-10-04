# 6.826 POCS Labs

## Lab 1: StatDB

In this lab, you will implement a database that supports adding numbers and
getting the mean of the numbers added so far. Your proof will connect the
implementation (which only tracks the count and the sum) to a specification that
tracks all the input numbers.

To run your code, compile with `make` and then run `./bin/statdb-cli`. Exit by
pressing `Ctrl-c`.

## Lab 2: Remapping a bad sector

In this lab, you will implement an interface to a disk that remaps addresses to
avoid a bad sector. We provide a specification
[BadBlockAPI](src/Lab2/BadBlockAPI.v) that has one bad sector in a known
location and a specification [OneDiskAPI](src/Common/OneDiskAPI.v) for a normal
disk. You will implement the clean one disk API on top of the bad block API (for
a disk that is one block smaller).

You can run your code as a Linux block device using NBD. If you're on macOS,
you'll need a Linux VM to try this out (you won't need to install Coq or Haskell
on it, though). **Running your code is optional** in this lab - we're only
checking your proofs. You should still run `make` to compile the Coq code and
make sure your proofs check.

### Overview of NBD

[Network Block Device (NBD)](https://nbd.sourceforge.io/) is a Linux kernel
feature that lets you use a remote server as a block device. Every time the
client reads or writes `/dev/nbd0`, nbd will make a request over TCP to the
server.

Ordinarily this lets you use disk space or devices from remote machines. We use
it to _implement_ a block device as a userspace program, then export it by
implementing the NBD protocol.

### Running the remapped disk as an NBD server

The high-level overview is that you'll run `remap-nbd` to start an NBD server
with your code, then connect to it from Linux with the standard Linux client,
`nbd-client`. Then reads and writes to the special block device `/dev/nbd0` will
be implemented using `remap-nbd` by running code extracted from Coq.

First, run `make` to compile the Coq code and `bin/remap-nbd`.

Once you've compiled, initialize the disk image (defaults to a 100MB disk):

```
./bin/remap-nbd init
```

And then run the server:

```
./bin/remap-nbd start [--debug]
```

The disk's contents are stored in `disk0.img` in the current directory.

First, load the `nbd` kernel module.

```
sudo modprobe nbd
```

Connect to it from a client:

```
sudo nbd-client localhost /dev/nbd0
```

Use it a bit (you can do this without sudo by adding yourself to the disk group:
`sudo usermod -a -G disk $USER`):

```
mkfs.ext4 -E root_owner /dev/nbd0
sudo mkdir /mnt/nbd
sudo mount /dev/nbd0 /mnt/nbd
mkdir /mnt/nbd/dir
echo "some text" > /mnt/nbd/foo
ls /mnt/nbd
sudo umount /mnt/nbd
```

Disconnect the block device:

```
sudo nbd-client -d /dev/nbd0
```

The `remap-nbd` server won't exit since it continually accepts new connections,
but you can send an interrupt signal with `Ctrl-C`.

## Notes

Please do not post your solutions publicly. We plan to use this material for
future editions of 6.826.
