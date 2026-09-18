# Triangular-lattice barriers for Erdős #1066

Erdős #1066 asks for the asymptotic guaranteed independent-set fraction in unit-distance graphs formed by planar point sets whose pairwise distances are at least one.

This note collects several elementary obstructions showing why the triangular lattice and related three-colorable constructions cannot by themselves improve the known upper-construction regime.

## 1. Three-colorable configurations have independence ratio at least one third

The Lean theorem

```text
card_le_three_mul_alpha_of_threeColouring
```

proves that for a finite graph with a proper three-coloring,

\[
|P|\le3\alpha(P).
\]

Equivalently,

\[
\alpha(P)\ge |P|/3.
\]

Thus any construction that remains three-colorable cannot realize an independent-set ratio below `1/3`.

## 2. The unit triangular lattice is three-colorable

For integers `x,y`, the arithmetic core is

\[
x^2+xy+y^2=1
\quad\Longrightarrow\quad
3\nmid(x-y).
\]

This is formalized as

```text
triangularLattice_colouring_proper.
```

Coloring a lattice point with coordinates `(a,b)` by

\[
(a-b)\bmod3
\]

therefore separates every pair at unit distance. The geometric theorem

```text
latticeColouring_proper
```

formalizes exactly this statement.

Hence every finite unit-distance graph induced by triangular-lattice points is three-colorable and has an independent set containing at least one third of its vertices.

## 3. Unit equilateral triangles have circumradius below one

For the standard unit equilateral triangle, the formal theorem

```text
unit_triangle_circumradius_sq
```

proves that the squared circumradius is

\[
\boxed{1/3},
\]

so the circumradius is strictly less than one.

The supporting theorem `unit_triangle` verifies the unit equilateral geometry, and `latticePoint_admissible` establishes the minimum-distance condition for lattice subsets.

## Consequence for lattice-based constructions

The triangular lattice is therefore structurally constrained in two independent ways:

- its unit-distance graph has a proper three-coloring;
- the local equilateral geometry has covering radius `1/sqrt(3)` at the triangle level.

The first point alone already shows that a purely three-colorable lattice construction cannot lower the independent-set ratio below `1/3`.

## Additional exact checks

The project also contains exact arithmetic computations for two further local questions:

- a degree-six lattice-rigidity check;
- lattice-closure calculations.

A separate normalization check shows that the Moser-spindle coordinates used in one attempted route are not admissible under the project's exact minimum-distance normalization, so that configuration cannot simply be imported into this formulation without rescaling and rechecking the hypotheses.

These are computational geometry checks and are kept distinct from the Lean theorems above.

## Formal status

The named theorems in this note have recorded axiom footprint

```text
{propext, Classical.choice, Quot.sound}.
```

The broader `Erdos1066.lean` module also contains the open conjecture, literature bounds, and several unfinished geometric lemmas as explicit `sorry` declarations. Those declarations are not dependencies of the proved barrier theorems listed here.

See [`../formalization/README.md`](../formalization/README.md) for the full declaration map.

## Mathematical scope

These results explain limitations of a particular geometric architecture; they are not an asymptotic solution of Erdős #1066. Their value is to remove several natural but insufficient construction routes and to provide reusable formal lemmas about the unit triangular lattice.

Author: Jared Wilder.
