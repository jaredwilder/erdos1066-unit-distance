# Erdős #1066 — Unit-Distance Graphs

**Jared Wilder**

Formal and computational work on Erdős Problem #1066, centered on independent-set bounds in unit-distance graphs.

This repository collects the project’s Lean formalization, exact finite checks, structural barriers, and remaining proof obligations in one place. The emphasis is on reusable mathematics: statements, proved lemmas, explicit counterpressure on failed routes, and machine-checkable artifacts.

## Contents

- `formalization/` — FormalConjectures-style Lean statements and proved supporting lemmas.
- `barriers/` — structural and local obstructions developed during the attack.
- finite checks and supporting artifacts used to test candidate arguments.

## Mathematical status

The repository contains proved intermediate results and formalized reductions toward Erdős #1066. The full parent problem remains open here; open obligations are kept explicit in the source rather than mixed with proved lemmas.

## Verification

Lean sources are intended to make the proof boundary mechanically visible: proved declarations compile, while conjectural or unfinished statements are identified at the point where they enter the argument.

## Provenance

This repository consolidates material previously released across the broader Wilder mathematics estate, including:

- `unpublished-math-papers/erdos1066-lattice-barriers/`
- `lean-contributions/erdos1066-first-formalization/`

The goal of this repository is a clean problem-level reading surface for the #1066 work.