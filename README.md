# A repository for PoS related formal methods

This repository contains some distributed consensus related stuff.

## An Alloy Experiment

`minimum-t.als` contains an Alloy experiment about a protocol.  Open the file with [Alloy 4.2](http://alloy.mit.edu/alloy/) and press "Execute" and then "Show".

In Alloy, *enable Options->Forbid Overflow*

## Some Casper Isabelle/HOL Proofs

Isabelle2017 should work.

### On the Newest Casper Design

* [`DynamicValidatorSetOneMessage.thy`](DynamicValidatorSetOneMessage.thy) is about one-message Casper (newer) with a dynamic validator set (more realistic), and proves accountable safety (not plausible liveness).

* [`CasperOneMessage.thy`](CasperOneMessage.thy) is about one-message Casper (newer) with a static validator set (unrealistic), and proves accountable safety (not plausible liveness).

### On Older Casper Designs

* [`DynamicValidatorSet.thy`](DynamicValidatorSet.thy) is about two-message Casper (older) with a dynamic validator set (more realistic), and proves accountable safety (not plausible liveness).

* [`Casper.thy`](Casper.thy) is about two-message Casper (older) with a static validator set (unrealistic), and proves accountable safety (not plausible liveness).

* [`MinimumAlgo.thy`](MinimumAlgo.thy) is about two-message Casper (older) with a dynamic validator set, and proves accountable safety and plausible liveness.

### How to See the Script

Open the `thy` files with Isabelle2017.

Or, adjust the path in `document_generation.sh` and run it to obtain a PDF file (which should look like [this one](https://yoichihirai.com/minimal.pdf)).

## License

All files are distributed under Apache License Version 2.0.  See `LICENSE`.
