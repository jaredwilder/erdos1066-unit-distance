# Erdős #1066 — triangular-lattice and 3-colourability barriers

**Author:** Jared Wilder  
**Campaign date:** 2026-07-25  
**Public release:** 2026-09-11

## Problem

Erdős #1066 asks about the asymptotic guaranteed independent-set fraction in unit-distance graphs formed by `n` planar points whose pairwise distances are at least one.

The source campaign formalized the problem and proved a collection of barrier lemmas in Lean. This release does **not** claim to solve #1066 or to move the published asymptotic bounds.

## Lean-certified barrier package

The source records the following theorem declarations as sorry-free, with independently probed axiom footprint

`[propext, Classical.choice, Quot.sound]`.

### B1 — any proper 3-colouring forces a one-third independent set

`card_le_three_mul_alpha_of_threeColouring`

For a finite graph with a proper 3-colouring,

`|P| <= 3 * alpha(P)`.

Equivalently, one colour class has size at least `|P|/3`.

### B2 core — arithmetic obstruction on the triangular lattice

`triangularLattice_colouring_proper`

For integers `x,y`,

`x^2 + xy + y^2 = 1`

implies

`3 ∤ (x-y)`.

This is the arithmetic core behind the standard 3-colouring of the triangular lattice by `(a-b) mod 3`.

### B2 geometric — triangular-lattice unit-distance colouring

`latticeColouring_proper`

Triangular-lattice points at Euclidean distance exactly one receive different colours under

`(a-b) mod 3`.

Hence every finite unit-distance graph induced by triangular-lattice points is 3-colourable.

### B3 core — unit equilateral triangle circumradius

`unit_triangle_circumradius_sq`

The squared circumradius of a unit equilateral triangle is exactly

`1/3 < 1`.

The source also records the supporting theorem `latticePoint_admissible`.

### Barrier consequence

`threeColouring_cannot_beat_pach_toth`

Any configuration that remains 3-colourable cannot improve an upper construction wall below `1/3`; in particular the triangular lattice cannot be the mechanism for beating a `5/16` asymptotic target.

The exact published-bound bookkeeping in the source is left external to these local barrier proofs.

### Definition-faithfulness theorem

`exists_indep_g`

The source records a theorem checking that the formal `sInf` definition used for `g(n)` really represents the largest independent-set size guaranteed across the admissible `n`-point configurations, rather than merely a type-correct surrogate.

## Additional exact computational checks

The campaign also reports exact multiquadratic-arithmetic checks for two further geometry barriers and a falsification:

- the degree-six lattice rigidity check (`B4`), performed outside the Lean core;
- lattice closure (`B5`), also exact-computational;
- the Moser spindle is **inadmissible at the campaign's exact squared-distance `1/3` geometric normalization**, so its ratio `2/7` cannot be imported as a competing #1066 configuration in that normalization.

These computational checks are kept distinct from the Lean-certified theorem list above.

## Scope / formalization honesty

The original Lean file compiled with nine `sorry` warnings, but the source explicitly records those warnings as belonging to:

- the still-open main problem;
- imported published results / external walls;
- named bookkeeping steps not claimed proved by this local package.

The barrier theorem declarations named above were separately probed with `#print axioms` and recorded as sorry-free.

This distinction matters: the file as a whole is not claimed completely sorry-free, while the local barrier theorems are.

## Novelty boundary

The source campaign reported that #1066 was absent from the FormalConjectures Erdős-problem corpus at the time and described this as a first formal statement. This public release **does not rely on or upgrade that priority claim**. The mathematical lemmas are published for provenance and reuse; historical/formalization priority remains a separate literature-and-repository question.