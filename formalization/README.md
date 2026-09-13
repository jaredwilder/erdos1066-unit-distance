# EG1066Formal — the first formal (Lean 4) statement of Erdős Problem #1066

**File:** `Erdos1066.lean`
**Date:** 2026-07-25
**Status of the problem upstream:** *not formalised anywhere.* The FormalConjectures corpus
(`oracle/runtime/state/formal-conjectures-checkout/FormalConjectures/ErdosProblems/`) contains 509
`.lean` problem files; `1066` is **not** among them (`1064.lean`, `1065.lean` and `1067.lean` are
present, `1066.lean` is not — verified by direct `ls`). erdosproblems.com also lists #1066 as
unformalised.

---

## The problem

Given `n` points in ℝ² with all pairwise distances ≥ 1, form the graph joining pairs at distance
exactly 1. Let `g(n)` be the largest number such that **every** such configuration has an
independent set of size ≥ `g(n)`. **Estimate `lim g(n)/n`.**

Published walls:

| Wall | Value | Source |
|---|---|---|
| lower | 8/31 ≈ 0.2581 | Swanepoel 2002 (improving 9/35 Csizmadia 1998, 1/4 Pollack 1985) |
| upper | 5/16 = 0.3125 | Pach–Tóth 1996 (improving 6/19 Chung–Graham / Pach) |

---

## What is in the file

Written in FormalConjectures house style (Apache-2.0 header, module docstring with the
`erdosproblems.com` reference, `@[category ...]` / `@[AMS ...]` attributes, `answer(sorry)` for the
unknown value, `erdos_1066.variants.*` naming). It imports `FormalConjecturesUtil` and compiles
inside the FormalConjectures checkout — see *How to verify* below.

Ambient space: `ℝ²` = `EuclideanSpace ℝ (Fin 2)` (the corpus' own scoped notation, from
`FormalConjecturesForMathlib.Geometry.2d`).

### Definitions (stated — these *are* the deliverable)

| Name | Meaning |
|---|---|
| `Admissible P` | every two distinct points of the finite set `P` are ≥ 1 apart |
| `IsUDIndep S` | no two distinct points of `S` are at distance exactly 1 (independence in the unit-distance graph) |
| `indepCards P` | the set of sizes of independent subsets of `P` |
| `alpha P` | `sSup (indepCards P)` — the independence number |
| `admissibleAlphas n` | `{alpha P : P admissible, ∣P∣ = n}` |
| `g n` | `sInf (admissibleAlphas n)` |
| `pt x y`, `latticePoint a b` | coordinates; the unit triangular lattice `a(1,0) + b(1/2,√3/2)` |
| `triA`,`triB`,`triC`,`triO` | the unit equilateral triangle and its circumcentre |

### PROVEN (no `sorry`, no axiom)

| Theorem | Content |
|---|---|
| `indepCards_bddAbove`, `zero_mem_indepCards` | the `sSup` in `alpha` is well-posed |
| `card_le_alpha`, `alpha_le_card` | `alpha` is the max over independent subsets |
| `exists_indep_card_eq_alpha` | the sup is **attained** (`Nat.sSup_mem`) |
| `g_le_alpha` | `g ∣P∣ ≤ alpha P` for admissible `P` |
| `exists_indep_g` | **faithfulness check**: every admissible `n`-set has an independent subset of size ≥ `g n` — i.e. the `sInf`-definition really is the "largest guaranteed independent set" of the problem statement |
| `exists_big_fibre` | pigeonhole: some colour class has ≥ `∣P∣/3` points |
| **`card_le_three_mul_alpha_of_threeColouring`** | **BARRIER B1**: a proper 3-colouring ⟹ `∣P∣ ≤ 3·alpha P` |
| `threeColouring_cannot_beat_pach_toth` | B1 consequence: `alpha P > (5/16)·∣P∣`, so a 3-colourable gadget can never move the upper wall |
| `dist_pt_sq` | squared Euclidean distance in coordinates |
| `dist_latticePoint_sq` | lattice distance² = `Δa² + ΔaΔb + Δb²` |
| **`triangularLattice_colouring_proper`** | **BARRIER B2 (core)**: `x²+xy+y² = 1` over ℤ ⟹ `3 ∤ (x−y)` |
| **`latticeColouring_proper`** | **BARRIER B2 (geometric)**: lattice points at distance exactly 1 get different colours under `(a−b) mod 3` |
| `latticePoint_admissible` | every subset of the triangular lattice is admissible |
| `unit_triangle` | `triA,triB,triC` is a unit equilateral triangle |
| **`unit_triangle_circumradius_sq`** | **BARRIER B3 (core)**: `triO` is equidistant from all three vertices at squared distance exactly `1/3`, and `1/3 < 1` — the circumradius of the unit equilateral triangle is `1/√3 < 1` |

### `sorry` — the conjecture and the published results (correctly left open)

| Theorem | Why `sorry` |
|---|---|
| `erdos_1066` | **the open problem itself**; the value is `answer(sorry)` |
| `erdos_1066.variants.limit_exists` | existence of the limit (superadditivity) |
| `erdos_1066.variants.pollack` | `g(n) ≥ n/4` — needs the Four Colour Theorem |
| `erdos_1066.variants.swanepoel_lower_bound` | 8/31, Swanepoel 2002 |
| `erdos_1066.variants.pach_toth_upper_bound` | 5/16, Pach–Tóth 1996 |
| `erdos_1066.variants.translate_reduction` | the disjoint-translate reduction: `lim ≤ alpha P / ∣P∣` for any finite admissible `P` |

### `sorry` — barrier steps that are genuinely not done

| Theorem | Missing step (stated honestly, not faked) |
|---|---|
| `lattice_subset_ratio_ge_one_third` | B2 full form. The colouring is proved proper (`latticeColouring_proper`); the missing part is bookkeeping — turning the `ℤ×ℤ`-indexed colouring into a total function `ℝ² → Fin 3` via a choice of lattice coordinates. Then B1 applies verbatim. |
| `triangularLattice_covering_radius` | B3 full form. The arithmetic input (circumradius² = 1/3) *is* proved; missing is the covering argument (the lattice triangulates the plane; the farthest point of an acute triangle from all vertices is the circumcentre). |
| `two_grains_not_admissible` | the geometric consequence of B3. |

**B4 (degree-6 rigidity) was deliberately not attempted** — it needs trigonometry (chord length
`2 sin(φ/2)`), out of scope for this pass.

---

## THE BAR — measured axiom footprint

Nothing here is closed by an axiom that assumes its own conclusion. There are **no `axiom`
declarations in this file at all** — every unproved statement is an explicit `sorry`, and every
claim in the PROVEN table above is a real Lean proof. A statement-only formalisation is a genuine
deliverable; a faked proof is worse than nothing.

This is not an assertion — it was **measured** with `#print axioms` on every theorem in the PROVEN
table (run on a scratch copy so the deliverable file stays clean):

```
'Erdos1066.indepCards_bddAbove'                        [propext, Classical.choice, Quot.sound]
'Erdos1066.zero_mem_indepCards'                        [propext, Classical.choice, Quot.sound]
'Erdos1066.card_le_alpha'                              [propext, Classical.choice, Quot.sound]
'Erdos1066.alpha_le_card'                              [propext, Classical.choice, Quot.sound]
'Erdos1066.exists_indep_card_eq_alpha'                 [propext, Classical.choice, Quot.sound]
'Erdos1066.g_le_alpha'                                 [propext, Classical.choice, Quot.sound]
'Erdos1066.exists_indep_g'                             [propext, Classical.choice, Quot.sound]
'Erdos1066.card_le_three_mul_alpha_of_threeColouring'  [propext, Classical.choice, Quot.sound]   ← B1
'Erdos1066.threeColouring_cannot_beat_pach_toth'       [propext, Classical.choice, Quot.sound]
'Erdos1066.dist_pt_sq'                                 [propext, Classical.choice, Quot.sound]
'Erdos1066.dist_latticePoint_sq'                       [propext, Classical.choice, Quot.sound]
'Erdos1066.triangularLattice_colouring_proper'         [propext, Classical.choice, Quot.sound]   ← B2 core
'Erdos1066.latticeColouring_proper'                    [propext, Classical.choice, Quot.sound]   ← B2 geometric
'Erdos1066.one_le_latticeNorm'                         [propext, Classical.choice, Quot.sound]
'Erdos1066.latticePoint_admissible'                    [propext, Classical.choice, Quot.sound]
'Erdos1066.unit_triangle'                              [propext, Classical.choice, Quot.sound]
'Erdos1066.unit_triangle_circumradius_sq'              [propext, Classical.choice, Quot.sound]   ← B3 core
```

`[propext, Classical.choice, Quot.sound]` is the standard Lean 4 / Mathlib base — **no `sorryAx`,
no project-local axiom, in any of them.** The `sorry`s are confined to the declarations listed in
the two `sorry` tables above, and none of the proven theorems depends on any of them.

---

## How to verify

The file has no lakefile of its own (it is a single module, and this directory owns no build
config). Compile it against the already-built Mathlib in the FormalConjectures checkout:

```bash
cd "oracle/runtime/state/formal-conjectures-checkout"
PATH="$HOME/.elan/bin:$PATH" lake env lean "<repo>/oracle/math/EG1066Formal/Erdos1066.lean"
```

Toolchain: `leanprover/lean4:v4.27.0`, Mathlib `v4.27.0` (pre-built oleans present in
`.lake/packages/mathlib/.lake/build/lib`). A full-Mathlib import takes roughly 10–15 minutes on
this Windows box. A clean run prints only `declaration uses 'sorry'` warnings, one per `sorry`
listed above, plus `linter.style.moduleDocstring` warnings for the `/-! ### ... -/` section
headers (cosmetic; silence with `set_option linter.style.moduleDocstring false` if upstreaming).

`bun oracle/scripts/lean-verify.ts --lean-path oracle/math/EG1066Formal/Erdos1066.lean
--project-root oracle/runtime/state/formal-conjectures-checkout` will exit **non-zero** — by
design, since that gate fails on any `sorry` leakage and this file intentionally contains `sorry`
for the open problem. That is the expected outcome, not a failure of the deliverable.

---

## If this is upstreamed

To contribute to FormalConjectures, copy `Erdos1066.lean` to
`FormalConjectures/ErdosProblems/1066.lean`, change the copyright header to
`Copyright 2026 The Formal Conjectures Authors` per their CLA, and drop the barrier lemmas that
are not part of the problem statement (or keep them as `@[category API]` — the corpus does carry
API lemmas, e.g. `unitDistanceCounts_BddAbove` in `90.lean`).
