/-
Copyright 2026 Jared Wilder.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 1066

*Reference:* [erdosproblems.com/1066](https://www.erdosproblems.com/1066)

Let $g(n)$ be the largest number such that **every** set of $n$ points in $\mathbb{R}^2$ with
pairwise distances all $\geq 1$ contains a subset of size $\geq g(n)$ in which no two points are
at distance exactly $1$.  Estimate $\lim g(n)/n$.

The published walls are
$$\tfrac{8}{31} = 0.2580\ldots \leq \lim \frac{g(n)}{n} \leq \tfrac{5}{16} = 0.3125,$$
the lower bound due to Swanepoel [Sw02] (improving $9/35$ of Csizmadia [Cs98] and $1/4$ of
Pollack [Po85], the latter from the Four Colour Theorem since these graphs are planar) and the
upper bound due to Pach–Tóth [PaTo96] (improving $6/19$ of Chung–Graham and, independently, Pach).

This file records:
* the **statement** of the problem (`erdos_1066`) together with the two walls and the
  disjoint-translate reduction which is the source of every upper bound;
* an **API** for the independence number `alpha` and for `g` itself, proving that `g n` really is
  the guarantee it is advertised to be (`exists_indep_g`);
* **barrier B1** (`card_le_three_mul_alpha_of_threeColouring`), fully proved: a $3$-colourable
  configuration has ratio $\geq 1/3 > 5/16$ and so can never move the upper wall;
* **barrier B2** (`triangularLattice_colouring_proper`, `latticeColouring_proper`), fully proved:
  $(a-b) \bmod 3$ is a proper $3$-colouring of the unit triangular lattice, so — via B1 — the
  search for a record must leave the lattice;
* **barrier B3** (`unit_triangle_circumradius_sq`), whose arithmetic core is fully proved: the
  circumradius of the unit equilateral triangle is $1/\sqrt3$, i.e. the covering radius of the
  triangular lattice is $1/\sqrt3 < 1$.

[Cs98] Csizmadia, G., _The multiplicity of the two smallest distances among points_.
Discrete Math. (1998), 67-74.

[PaTo96] Pach, J. and Tóth, G., _On the independence number of coin graphs_.
Geombinatorics (1996), 30-33.

[Po85] Pollack, R., _Increasing the minimum distance of a set of points_.
Discrete Comput. Geom. (1985), 321.

[Sw02] Swanepoel, K. J., _Independence numbers of planar contact graphs_.
Discrete Comput. Geom. (2002), 649-670.
-/

open Filter

open scoped EuclideanGeometry Topology

namespace Erdos1066

/-
### The objects
-/

/--
A finite set of points in the plane is **admissible** when every two distinct points are at
distance at least $1$.  This is the minimum-separation hypothesis of the problem.
-/
def Admissible (P : Finset ℝ²) : Prop :=
  (P : Set ℝ²).Pairwise fun p q => 1 ≤ dist p q

/--
A finite set of points is **independent** for the unit-distance graph when no two distinct
points of it are at distance exactly $1$.  (The unit-distance graph of `P` is
`SimpleGraph.UnitDistancePlaneGraph ↑P`; this predicate is exactly independence in that graph.)
-/
def IsUDIndep (S : Finset ℝ²) : Prop :=
  (S : Set ℝ²).Pairwise fun p q => dist p q ≠ 1

/-- The set of sizes of independent subsets of `P`. -/
def indepCards (P : Finset ℝ²) : Set ℕ :=
  {k | ∃ S ⊆ P, IsUDIndep S ∧ S.card = k}

/--
The **independence number** of the unit-distance graph on `P`, i.e. the largest size of a subset
of `P` containing no two points at distance exactly $1$.
-/
noncomputable def alpha (P : Finset ℝ²) : ℕ := sSup (indepCards P)

/-- The set of independence numbers of admissible `n`-point configurations. -/
def admissibleAlphas (n : ℕ) : Set ℕ :=
  {k | ∃ P : Finset ℝ², Admissible P ∧ P.card = n ∧ alpha P = k}

/--
$g(n)$: the largest number such that **every** admissible set of $n$ points in the plane has an
independent set of size at least $g(n)$; equivalently the minimum of `alpha` over all admissible
$n$-point configurations.  That the two descriptions agree is `exists_indep_g` together with
`g_le_alpha`.
-/
noncomputable def g (n : ℕ) : ℕ := sInf (admissibleAlphas n)

/-
### API for `alpha` and `g`
-/

@[category API, AMS 5 52]
theorem indepCards_bddAbove (P : Finset ℝ²) : BddAbove (indepCards P) := by
  refine ⟨P.card, ?_⟩
  rintro k ⟨S, hSP, -, rfl⟩
  exact Finset.card_le_card hSP

@[category API, AMS 5 52]
theorem zero_mem_indepCards (P : Finset ℝ²) : 0 ∈ indepCards P :=
  ⟨∅, Finset.empty_subset _, by simp [IsUDIndep], rfl⟩

@[category API, AMS 5 52]
theorem card_le_alpha {P S : Finset ℝ²} (hSP : S ⊆ P) (hS : IsUDIndep S) : S.card ≤ alpha P :=
  le_csSup (indepCards_bddAbove P) ⟨S, hSP, hS, rfl⟩

@[category API, AMS 5 52]
theorem alpha_le_card (P : Finset ℝ²) : alpha P ≤ P.card :=
  csSup_le ⟨0, zero_mem_indepCards P⟩ (by rintro k ⟨S, hSP, -, rfl⟩; exact Finset.card_le_card hSP)

/-- The supremum defining `alpha` is attained: there is an independent subset of that exact size. -/
@[category API, AMS 5 52]
theorem exists_indep_card_eq_alpha (P : Finset ℝ²) :
    ∃ S ⊆ P, IsUDIndep S ∧ S.card = alpha P :=
  Nat.sSup_mem ⟨0, zero_mem_indepCards P⟩ (indepCards_bddAbove P)

@[category API, AMS 5 52]
theorem g_le_alpha {P : Finset ℝ²} (hP : Admissible P) : g P.card ≤ alpha P :=
  Nat.sInf_le ⟨P, hP, rfl, rfl⟩

/--
`g n` really is a guarantee: **every** admissible `n`-point configuration contains an independent
set of size at least `g n`.  This is the defining property quoted in the problem statement.
-/
@[category API, AMS 5 52]
theorem exists_indep_g {n : ℕ} (P : Finset ℝ²) (hP : Admissible P) (hcard : P.card = n) :
    ∃ S ⊆ P, IsUDIndep S ∧ g n ≤ S.card := by
  obtain ⟨S, hSP, hS, hcardS⟩ := exists_indep_card_eq_alpha P
  refine ⟨S, hSP, hS, ?_⟩
  have h1 : g n ≤ alpha P := by rw [← hcard]; exact g_le_alpha hP
  omega

/-
### The problem
-/

/--
Let $g(n)$ be the largest number such that any set of $n$ points in $\mathbb{R}^2$ with all
pairwise distances at least $1$ contains an independent set of size $\geq g(n)$ in the
unit-distance graph.  **Estimate $\lim g(n)/n$.**
-/
@[category research open, AMS 5 52]
theorem erdos_1066 :
    Tendsto (fun n : ℕ => (g n : ℝ) / n) atTop (𝓝 (answer(sorry))) := by
  sorry

/--
The limit exists.  (This is a consequence of superadditivity of `g`; it is not the content of the
problem, which asks for its value.)
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.limit_exists :
    ∃ c : ℝ, Tendsto (fun n : ℕ => (g n : ℝ) / n) atTop (𝓝 c) := by
  sorry

/--
Pollack [Po85]: $g(n) \geq n/4$, from the Four Colour Theorem — the unit-distance graph of a
minimum-separated planar set is planar.
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.pollack (n : ℕ) : (n : ℝ) / 4 ≤ g n := by
  sorry

/--
Swanepoel [Sw02]: the lower wall $\lim g(n)/n \geq 8/31$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.swanepoel_lower_bound (c : ℝ)
    (hc : Tendsto (fun n : ℕ => (g n : ℝ) / n) atTop (𝓝 c)) : 8 / 31 ≤ c := by
  sorry

/--
Pach–Tóth [PaTo96]: the upper wall $\lim g(n)/n \leq 5/16$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.pach_toth_upper_bound (c : ℝ)
    (hc : Tendsto (fun n : ℕ => (g n : ℝ) / n) atTop (𝓝 c)) : c ≤ 5 / 16 := by
  sorry

/--
**The disjoint-translate reduction.**  Every finite admissible configuration `P` is an upper
bound for the limit: placing `k` far-separated translates of `P` produces an admissible
`k|P|`-point set whose unit-distance graph is `k` disjoint copies of that of `P`, so its
independence number is exactly `k·alpha P`.  Hence a single finite gadget of small ratio is a
complete certificate for an upper bound, which is why the upper wall is the computationally
attackable side.
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.translate_reduction (P : Finset ℝ²) (hP : Admissible P)
    (hne : P.Nonempty) (c : ℝ) (hc : Tendsto (fun n : ℕ => (g n : ℝ) / n) atTop (𝓝 c)) :
    c ≤ (alpha P : ℝ) / P.card := by
  sorry

/-
### Barrier B1 — the 3-colourability barrier

If the unit-distance graph of `P` is $3$-colourable then the largest colour class is independent
and has size $\geq |P|/3$.  Since $1/3 > 5/16$, **no $3$-colourable gadget can ever move the upper
wall.**  This is fully proved.
-/

/-- Pigeonhole: some fibre of a `Fin 3`-valued map on `P` has at least `|P|/3` elements. -/
private theorem exists_big_fibre {α : Type*} [DecidableEq α] (P : Finset α) (col : α → Fin 3) :
    ∃ i : Fin 3, P.card ≤ 3 * (P.filter fun p => col p = i).card := by
  by_contra h
  push_neg at h
  have hsum : P.card = ∑ i : Fin 3, (P.filter fun p => col p = i).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => Finset.mem_univ (col x)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [Fin.sum_univ_three] at hsum
  omega

/--
**Barrier B1.**  If `col` is a proper $3$-colouring of the unit-distance graph on `P` (points of
the same colour are never at distance exactly $1$), then $|P| \leq 3\,\alpha(P)$, i.e. the
independence ratio of `P` is at least $1/3$.
-/
@[category API, AMS 5 52]
theorem card_le_three_mul_alpha_of_threeColouring (P : Finset ℝ²) (col : ℝ² → Fin 3)
    (hcol : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → col p = col q → dist p q ≠ 1) :
    P.card ≤ 3 * alpha P := by
  classical
  obtain ⟨i, hi⟩ := exists_big_fibre P col
  refine hi.trans (Nat.mul_le_mul_left 3 (card_le_alpha (Finset.filter_subset _ _) ?_))
  intro p hp q hq hpq
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
  exact hcol p hp.1 q hq.1 hpq (hp.2.trans hq.2.symm)

/--
Consequence of B1: a $3$-colourable configuration has ratio at least $1/3 > 5/16$, so it can
never certify an improvement of the Pach–Tóth upper wall.
-/
@[category API, AMS 5 52]
theorem threeColouring_cannot_beat_pach_toth (P : Finset ℝ²) (col : ℝ² → Fin 3)
    (hcol : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → col p = col q → dist p q ≠ 1) :
    (5 : ℝ) / 16 * P.card < alpha P ∨ P.card = 0 := by
  rcases Nat.eq_zero_or_pos P.card with h | h
  · exact Or.inr h
  · refine Or.inl ?_
    have hb := card_le_three_mul_alpha_of_threeColouring P col hcol
    have hb' : (P.card : ℝ) ≤ 3 * alpha P := by exact_mod_cast hb
    have hpos : (0 : ℝ) < P.card := by exact_mod_cast h
    nlinarith

/-
### Coordinates in the plane
-/

/-- The point of `ℝ²` with coordinates `(x, y)`. -/
noncomputable def pt (x y : ℝ) : ℝ² := WithLp.toLp 2 ![x, y]

@[simp]
theorem pt_zero (x y : ℝ) : pt x y 0 = x := rfl

@[simp]
theorem pt_one (x y : ℝ) : pt x y 1 = y := rfl

/-- The squared Euclidean distance in coordinates. -/
@[category API, AMS 52]
theorem dist_pt_sq (x y x' y' : ℝ) :
    dist (pt x y) (pt x' y') ^ 2 = (x - x') ^ 2 + (y - y') ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-
### Barrier B2 — the triangular-lattice barrier

Let $T$ be the unit triangular lattice, $T = \{a(1,0) + b(1/2,\sqrt3/2) : a,b\in\mathbb Z\}$.
Every nonzero difference has squared length $a^2+ab+b^2 \geq 1$, so **every** subset of $T$ is
admissible, and two lattice points are at distance exactly $1$ iff $a^2+ab+b^2 = 1$.
The map $(a,b) \mapsto (a-b) \bmod 3$ is then a proper $3$-colouring, so by B1 every subset of the
triangular lattice has independence ratio $\geq 1/3$: **a record must leave the lattice.**
This is fully proved.
-/

/-- The lattice point $a(1,0) + b(1/2,\sqrt3/2)$ of the unit triangular lattice. -/
noncomputable def latticePoint (a b : ℤ) : ℝ² :=
  pt ((a : ℝ) + (b : ℝ) / 2) ((b : ℝ) * Real.sqrt 3 / 2)

/-- The squared distance between two triangular-lattice points is the lattice norm
$\Delta a^2 + \Delta a\,\Delta b + \Delta b^2$ of their difference. -/
@[category API, AMS 11 52]
theorem dist_latticePoint_sq (a b a' b' : ℤ) :
    dist (latticePoint a b) (latticePoint a' b') ^ 2
      = ((a : ℝ) - a') ^ 2 + ((a : ℝ) - a') * ((b : ℝ) - b') + ((b : ℝ) - b') ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [latticePoint, latticePoint, dist_pt_sq]
  linear_combination ((b : ℝ) - b') ^ 2 / 4 * h3

/--
**Barrier B2, arithmetic core.**  The only integer solutions of $x^2+xy+y^2 = 1$ are the six
units $(\pm1,0), (0,\pm1), (1,-1), (-1,1)$, and for each of them $x - y \not\equiv 0 \pmod 3$.
-/
@[category API, AMS 11]
theorem triangularLattice_colouring_proper (x y : ℤ) (h : x ^ 2 + x * y + y ^ 2 = 1) :
    ¬ (3 : ℤ) ∣ (x - y) := by
  have hy1 : y ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * x + y)]
  have hx1 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x + 2 * y)]
  have hy : -1 ≤ y ∧ y ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have hx : -1 ≤ x ∧ x ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  obtain ⟨hy0, hy2⟩ := hy
  obtain ⟨hx0, hx2⟩ := hx
  interval_cases x <;> interval_cases y <;> revert h <;> decide

/--
**Barrier B2, geometric form.**  Two triangular-lattice points at distance exactly $1$ get
different colours under $(a,b) \mapsto (a-b) \bmod 3$, i.e. that map is a proper $3$-colouring of
the unit-distance graph of the lattice.
-/
@[category API, AMS 11 52]
theorem latticeColouring_proper (a b a' b' : ℤ)
    (h : dist (latticePoint a b) (latticePoint a' b') = 1) :
    (a - b) % 3 ≠ (a' - b') % 3 := by
  have hsq : dist (latticePoint a b) (latticePoint a' b') ^ 2 = 1 := by rw [h]; norm_num
  rw [dist_latticePoint_sq] at hsq
  have hz : (a - a') ^ 2 + (a - a') * (b - b') + (b - b') ^ 2 = 1 := by
    have : (((a - a') ^ 2 + (a - a') * (b - b') + (b - b') ^ 2 : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
      push_cast
      linarith [hsq]
    exact_mod_cast this
  have := triangularLattice_colouring_proper (a - a') (b - b') hz
  omega

/--
The lattice norm $x^2+xy+y^2$ of a nonzero integer vector is at least $1$.
-/
@[category API, AMS 11]
theorem one_le_latticeNorm (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) : 1 ≤ x ^ 2 + x * y + y ^ 2 := by
  have hy : y = 0 ∨ y ≤ -1 ∨ 1 ≤ y := by omega
  rcases hy with rfl | hy | hy
  · have hx : x ≠ 0 := by
      rcases h with h | h
      · exact h
      · exact absurd rfl h
    have hx' : x ≤ -1 ∨ 1 ≤ x := by omega
    rcases hx' with hx' | hx' <;> nlinarith
  · nlinarith [sq_nonneg (2 * x + y)]
  · nlinarith [sq_nonneg (2 * x + y)]

/--
Every finite subset of the triangular lattice is admissible: distinct lattice points are at
squared distance $a^2+ab+b^2 \geq 1$.
-/
@[category API, AMS 11 52]
theorem latticePoint_admissible (a b a' b' : ℤ) (h : a ≠ a' ∨ b ≠ b') :
    1 ≤ dist (latticePoint a b) (latticePoint a' b') := by
  have hz : (1 : ℤ) ≤ (a - a') ^ 2 + (a - a') * (b - b') + (b - b') ^ 2 :=
    one_le_latticeNorm _ _ (by omega)
  have hr : (1 : ℝ) ≤ dist (latticePoint a b) (latticePoint a' b') ^ 2 := by
    rw [dist_latticePoint_sq]
    have : ((1 : ℤ) : ℝ) ≤ (((a - a') ^ 2 + (a - a') * (b - b') + (b - b') ^ 2 : ℤ) : ℝ) :=
      Int.cast_le.mpr hz
    push_cast at this
    linarith
  nlinarith [dist_nonneg (x := latticePoint a b) (y := latticePoint a' b')]

/--
**Barrier B2, full form.**  Every finite subset of the triangular lattice has independence ratio
at least $1/3$, hence can never move the Pach–Tóth upper wall.

*Only stated.*  It follows from `latticeColouring_proper` and
`card_le_three_mul_alpha_of_threeColouring`; the missing step is the bookkeeping that turns the
`ℤ × ℤ`-indexed colouring into a function `ℝ² → Fin 3` (a choice of lattice coordinates for each
point of `P`, which exists because `latticePoint` is injective).
-/
@[category API, AMS 11 52]
theorem lattice_subset_ratio_ge_one_third (P : Finset ℝ²)
    (hP : ∀ p ∈ P, ∃ a b : ℤ, p = latticePoint a b) :
    P.card ≤ 3 * alpha P := by
  sorry

/-
### Barrier B3 — the covering-radius barrier

The circumradius of the unit equilateral triangle is $1/\sqrt3$, so the covering radius of the
unit triangular lattice is $1/\sqrt3 < 1$: every point of the plane is within $1/\sqrt3$ of a
lattice point.  Hence two large triangular-lattice patches in **any** relative position always
produce a pair of points closer than $1$, so no union of two grains is admissible; dense
admissible sets are essentially a single grain, and by B2 a single grain has ratio $\geq 1/3$.
The arithmetic core below is fully proved.
-/

/-- Vertex `(0,0)` of the unit equilateral triangle. -/
noncomputable def triA : ℝ² := pt 0 0

/-- Vertex `(1,0)` of the unit equilateral triangle. -/
noncomputable def triB : ℝ² := pt 1 0

/-- Vertex `(1/2, √3/2)` of the unit equilateral triangle. -/
noncomputable def triC : ℝ² := pt (1 / 2) (Real.sqrt 3 / 2)

/-- The circumcentre `(1/2, √3/6)` of the unit equilateral triangle. -/
noncomputable def triO : ℝ² := pt (1 / 2) (Real.sqrt 3 / 6)

/-- `triA`, `triB`, `triC` really do form a unit equilateral triangle. -/
@[category API, AMS 52]
theorem unit_triangle :
    dist triA triB = 1 ∧ dist triB triC = 1 ∧ dist triA triC = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : ∀ u v : ℝ², dist u v ^ 2 = 1 → dist u v = 1 := by
    intro u v h
    nlinarith [dist_nonneg (x := u) (y := v)]
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_⟩
  · rw [triA, triB, dist_pt_sq]; norm_num
  · rw [triB, triC, dist_pt_sq]; linear_combination h3 / 4
  · rw [triA, triC, dist_pt_sq]; linear_combination h3 / 4

/--
**Barrier B3, arithmetic core.**  The point `triO = (1/2, √3/6)` is equidistant from the three
vertices of the unit equilateral triangle, at squared distance exactly $1/3$; and $1/3 < 1$.
So the circumradius of the unit equilateral triangle is $1/\sqrt3 < 1$.
-/
@[category API, AMS 52]
theorem unit_triangle_circumradius_sq :
    dist triO triA ^ 2 = 1 / 3 ∧ dist triO triB ^ 2 = 1 / 3 ∧ dist triO triC ^ 2 = 1 / 3 ∧
      (1 : ℝ) / 3 < 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · rw [triO, triA, dist_pt_sq]; linear_combination h3 / 36
  · rw [triO, triB, dist_pt_sq]; linear_combination h3 / 36
  · rw [triO, triC, dist_pt_sq]; linear_combination h3 / 9

/--
**Barrier B3, full form.**  The covering radius of the unit triangular lattice is $1/\sqrt3$:
every point of the plane lies within $1/\sqrt3$ of some lattice point.

*Only stated.*  The arithmetic input — that the circumradius of the unit equilateral triangle is
$1/\sqrt3$ — is `unit_triangle_circumradius_sq`; what is missing is the covering argument (the
lattice triangulates the plane, and the farthest point of an acute triangle from all three
vertices is its circumcentre).
-/
@[category API, AMS 52]
theorem triangularLattice_covering_radius (z : ℝ²) :
    ∃ a b : ℤ, dist z (latticePoint a b) ≤ Real.sqrt 3 / 3 := by
  sorry

/--
**Consequence of B3.**  No union of two full triangular-lattice grains, in any relative position
other than a lattice symmetry, is admissible.

*Only stated.*
-/
@[category API, AMS 52]
theorem two_grains_not_admissible (f : ℝ² → ℝ²) (hf : Isometry f)
    (hne : ∃ a b : ℤ, ∀ a' b' : ℤ, f (latticePoint a b) ≠ latticePoint a' b') :
    ∃ (a b a' b' : ℤ), dist (latticePoint a b) (f (latticePoint a' b')) < 1 := by
  sorry

end Erdos1066
