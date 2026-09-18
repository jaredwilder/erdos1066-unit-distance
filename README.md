# Erdős #1066 — independent sets in unit-distance graphs

Given `n` points in the plane with all pairwise distances at least one, join two points when their distance is exactly one. Let `g(n)` be the largest integer such that every such `n`-point configuration contains an independent set of size at least `g(n)`.

Erdős #1066 asks for the asymptotic behaviour of `g(n)/n`. This repository contains a Lean formalization of that extremal quantity and several proved geometric lemmas explaining why some natural constructions cannot improve the known upper-side mechanisms.

## A formal definition of the extremal function

[`formalization/Erdos1066.lean`](formalization/Erdos1066.lean) defines:

- admissible finite planar point sets, with pairwise distance at least one;
- independent subsets for the unit-distance graph;
- the independence number `alpha P`;
- the extremal function `g n` as the minimum independence number over admissible `n`-point configurations.

The file proves the basic API needed to show that these definitions have the intended meaning. In particular:

- `alpha P` is attained by an independent subset;
- `g |P| ≤ alpha P` for every admissible `P`;
- every admissible `n`-point set contains an independent subset of size at least `g n`.

These declarations are proved in Lean with the standard Mathlib classical axiom footprint and do not depend on the `sorry` declarations used for the open problem or cited literature bounds.

## Three-colourability gives a one-third independent set

A general graph-theoretic lemma in the formalization proves that any proper 3-colouring of a finite graph forces an independent set containing at least one third of the vertices:

\[
|P|\le 3\alpha(P).
\]

This is elementary, but it is useful here because it immediately identifies a limitation of lattice constructions that remain 3-colourable.

## The triangular lattice is properly 3-colourable

Write triangular-lattice points as

\[
a(1,0)+b\left(\frac12,\frac{\sqrt3}{2}\right),\qquad a,b\in\mathbb Z.
\]

The squared distance between two lattice points is

\[
\Delta a^2+\Delta a\,\Delta b+\Delta b^2.
\]

The Lean development proves the arithmetic core

\[
x^2+xy+y^2=1\quad\Longrightarrow\quad 3\nmid(x-y),
\]

and from it the geometric statement that colouring a lattice point by

\[
(a-b)\bmod 3
\]

is proper for unit-distance edges.

Thus every finite unit-distance graph induced by triangular-lattice points is 3-colourable, and the preceding lemma forces an independent set of size at least one third of its vertices.

The proofs are recorded as `triangularLattice_colouring_proper`, `latticeColouring_proper`, and `card_le_three_mul_alpha_of_threeColouring`.

## Unit equilateral triangles

The formalization also proves that the circumradius squared of a unit equilateral triangle is

\[
\boxed{\frac13<1}.
\]

This is the exact arithmetic input behind a second geometric obstruction route: the centre of a unit equilateral triangle lies less than unit distance from all three vertices. The remaining plane-covering step for that route is stated separately and is not silently treated as proved.

## What is proved and what is still a statement

The main open problem, the existence of the limiting value, and the published asymptotic bounds are represented in Lean but remain explicitly marked with `sorry`. The proved local results are separated from those statements.

A detailed theorem-by-theorem account is in:

- [`formalization/README.md`](formalization/README.md) — definitions, proved declarations, and open formal statements;
- [`barriers/README.md`](barriers/README.md) — the 3-colouring, triangular-lattice, and circumradius arguments.

## Build

The repository includes a Lean toolchain pin and `lakefile.lean`. The mathematical source is under `formalization/`.

Historical source copies from the wider research archive were consolidated here so the problem can be read from one subject-level repository rather than reconstructed from session artifacts.

Author: Jared Wilder.