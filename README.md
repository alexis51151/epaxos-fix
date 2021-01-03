# Fixing Egalitarian Paxos

## Highlights

- There is a problem in the TLA+ specification and the Golang implementation of [Egalitarian Paxos](https://github.com/efficient/epaxos).
- A counter-example in TLA+ is provided (under `tla+/CounterExample.cfg`).
- The counter-example can be executed with the following command: `docker run --rm -ti 0track/epaxos-counter-example:latest`.
- The algorithm reaches a state in which processes disagree on the dependencies of a command; this breaks safety.
- A detailed explanation of the problem is available [here](
http://arxiv.org/abs/1906.10917).

## Fix

- There is a fix available relatively to the problem raised by Pierre Sutra (under `tla+/EgalitarianPaxosFix.tla`).
- The fix is based on a new var called `vbal` which stores the last ballot at which a replica has voted.

## Proof of correctness

- A proof of correctness for the resulting algorithm is provided (under `papers/EPaxosProofs.pdf`).
- It aims at being proven formally by model checking.

## Authors

- Alexis Le Glaunec
- Pierre Sutra
