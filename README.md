# CSPEC

[![Build Status](https://travis-ci.com/mit-pdos/cspec.svg?branch=master)](https://travis-ci.com/mit-pdos/cspec)

Framework for reasoning about concurrent code using abstraction, layers, and movers.

## Compiling

You'll need Coq v8.9 or master and Go.

To compile CSPEC, CMAIL, and GoMail, run `make`. A benchmarking binary for
`CMAIL` is output to `bin/mail-test` and a GoMail binary that listens for SMTP
and POP3 connections is output to `bin/gomail`.
