# Lean formalization of Erdős #1066

`Erdos1066.lean` formalizes the unit-distance independent-set problem and proves a supporting API for its extremal function, triangular-lattice coloring, and elementary geometric barriers.

The main open problem is represented as a statement, while proved lemmas and imported/published bounds remain visibly separate in the source.

## Problem statement

Given `n` points in `R^2` with all pairwise distances at least one, join two points when their distance is exactly one. Let `g(n)` be the largest integer such that every admissible `n`-point configuration contains an independent set of size at least `g(n)`.

The asymptotic problem is to estimate

\[
\lim_{n\to\infty}\frac{g(n)}n.
\]

The source records the published bounds

| bound | value | reference |
|---|---:|---|
| lower | `8/31 ≈ 0.2581` | Swanepoel (2002), improving Csizmadia and Pollack |
| upper | `5/16 = 0.3125` | Pach–Tóth (1996), improving earlier constructions |

Those literature bounds are represented in Lean but are not reproved in this file.

## Definitions

The ambient plane is `EuclideanSpace R (Fin 2)`. The main definitions are:

| Lean name | Mathematical meaning |
|---|---|
| `Admissible P` | distinct points of `P` are at distance at least one |
| `IsUDIndep S` | no two distinct points of `S` are at distance exactly one |
| `indepCards P` | cardinalities of independent subsets of `P` |
| `alpha P` | independence number of the unit-distance graph on `P` |
| `admissibleAlphas n` | independence numbers of admissible `n`-point configurations |
| `g n` | minimum guaranteed independence number |
| `latticePoint a b` | point in the unit triangular lattice |
| `triA`, `triB`, `triC`, `triO` | unit equilateral triangle and circumcenter |

## Proved Lean theorems

The following declarations have complete proofs in the file and recorded axiom footprint

```text
{propext, Classical.choice, Quot.sound}.
```

### Extremal-function API

- `indepCards_bddAbove`, `zero_mem_indepCards` — well-posedness of the finite supremum defining `alpha`;
- `card_le_alpha`, `alpha_le_card` — `alpha` is the maximum size of an independent subset;
- `exists_indep_card_eq_alpha` — the maximum is attained;
- `g_le_alpha` — every admissible configuration has independence number at least `g`;
- `exists_indep_g` — every admissible `n`-point configuration contains an independent subset of size at least `g n`.

The last theorem is the source-fidelity check that the formal `sInf` definition of `g` has the intended extremal meaning.

### Three-coloring bound

`card_le_three_mul_alpha_of_threeColouring` proves that a proper three-coloring gives

\[
|P|\le3\alpha(P).
\]

Consequently any three-colorable construction has independent-set density at least `1/3`; in particular it cannot realize an upper construction below the published `5/16` benchmark.

### Triangular-lattice coloring

The file proves

\[
x^2+xy+y^2=1\quad\Longrightarrow\quad3\nmid(x-y)
\]

for integers `x,y`. This is the arithmetic core of the standard triangular-lattice coloring by `(a-b) mod 3`.

`latticeColouring_proper` lifts the arithmetic statement to geometry: triangular-lattice points at Euclidean distance one receive different colors.

`latticePoint_admissible` proves that triangular-lattice subsets satisfy the minimum-distance condition.

### Unit equilateral triangle

`unit_triangle` verifies the unit equilateral configuration. `unit_triangle_circumradius_sq` proves that its circumradius squared is exactly

\[
\frac13<1.
\]

## Statements not proved in this file

The source deliberately separates incomplete or externally supplied statements from the proved API.

### Main problem and literature statements

The following remain `sorry` in this module:

- `erdos_1066` — the open problem itself;
- `erdos_1066.variants.limit_exists` — existence of the asymptotic limit;
- the Pollack, Swanepoel, and Pach–Tóth literature bounds;
- the disjoint-translate reduction used to turn finite constructions into asymptotic upper bounds.

### Geometric completion steps

Three local geometric statements are also unfinished:

- `lattice_subset_ratio_ge_one_third` — packaging the lattice coloring as the required total coloring statement;
- `triangularLattice_covering_radius` — the covering-radius theorem for the triangular lattice;
- `two_grains_not_admissible` — the corresponding geometric consequence.

The degree-six rigidity route was not formalized in this module.

## Axiom audit

The proved declarations were checked with `#print axioms`. Their reported footprint is the standard Mathlib classical base

```text
[propext, Classical.choice, Quot.sound]
```

with no project-declared axiom and no dependence on the unfinished declarations above.

The module as a whole contains `sorry` because it also stores the open conjecture, literature statements, and unfinished geometric lemmas. Proof status should therefore be read declaration-by-declaration rather than inferred from compilation of the whole file.

## Build environment

The historical source was developed against Lean `v4.27.0` and the corresponding Mathlib/FormalConjectures checkout. The public repository now also contains its own top-level Lean project files; see the repository root for the current build entry point.

The original source was written in FormalConjectures style, including its category/AMS attributes and `erdos_1066.variants.*` namespace structure.

## Formalization provenance

At the time this file was written in July 2026, the checked FormalConjectures Erdős-problem directory did not contain a `1066.lean` entry. That observation is retained as provenance; it is not used here as a global priority claim.

Author: Jared Wilder.
