# A repository for PoS related formal methods

This repository contains some distributed consensus related stuff.

## An Alloy Experiment

`minimum-t.als` contains an Alloy experiment about a protocol.  Open the file with [Alloy 4.2](http://alloy.mit.edu/alloy/) and press "Execute" and then "Show".

In Alloy, *enable Options->Forbid Overflow*

## Some Isabelle/HOL Proofs

`Casper.thy` contains a very short proof about the safety property of a protocol.

`MinimumAlgo.thy` contains some older, 100x longer proofs about safety and liveness of the same protocol.  Open the file with [Isabelle 2016-1](http://isabelle.in.tum.de/).

Or, adjust the path in `document_generation.sh` and run it to obtain a PDF file (which should look like [this one](https://yoichihirai.com/minimal.pdf)).

## License

All files are distributed under Apache License Version 2.0.  See `LICENSE`.
