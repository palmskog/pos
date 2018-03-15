# A repository for PoS related formal methods

This repository contains some distributed consensus related stuff.

## An Alloy Experiment

`minimum-t.als` contains an Alloy experiment about a protocol.  Open the file with [Alloy 4.2](http://alloy.mit.edu/alloy/) and press "Execute" and then "Show".

In Alloy, *enable Options->Forbid Overflow*

## Some Isabelle/HOL Proofs

Isabelle2017 should work.

### On the Newest Casper Design

`DynamicValidatorSetOneMessage.thy` is about one-message casper (newer) with dynamic validator sets (more realistic), and proves the accountable safety (not the plausible liveness).

### On Older Casper Designs

`DynamicValidatorSet.thy` is about one-message casper (newer) with a constant validator set (unrealistic), and proves the accountable safety (not the plausible liveness).

`Casper.thy` is about two-message casper (older) with dynamic validator sets, and proves the accountable safety (not the plausible liveness).

`MinimumAlgo.thy` is about two-message casper (older) with dynamic validator sets, and proves the accountable safety and the plausible liveness.

### How to See the Script

Open the `thy` files with Isabelle2017.

Or, adjust the path in `document_generation.sh` and run it to obtain a PDF file (which should look like [this one](https://yoichihirai.com/minimal.pdf)).

## License

All files are distributed under Apache License Version 2.0.  See `LICENSE`.
