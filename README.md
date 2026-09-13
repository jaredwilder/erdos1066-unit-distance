# Erdős #1066 — unit-distance independent-set program

**Author:** Jared Wilder  
**Status:** formalization / barrier / explicit-obligation program; the parent open problem is **not claimed solved**.

This repository is the canonical public home for the estate's #1066 work on unit-distance graphs and independent-set bounds. It consolidates the substantial FormalConjectures-style module, proved API/local barriers, exact finite checks, and explicitly unfinished obligations.

## Reading rule

Statement formalization is not theorem proof. Kernel-clean API lemmas are separated from open conjecture statements, compiler-trusted computations, and unfinished proof obligations.

## Source layout

Exact public source bytes are migrated under:

- `barriers/` — `unpublished-math-papers/erdos1066-lattice-barriers/`;
- `formalization/` — `lean-contributions/erdos1066-first-formalization/`.

The repository keeps proved/open boundaries explicit rather than letting a large Lean surface imply a closure claim.
