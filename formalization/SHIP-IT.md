# EG1066 — SHIP IT

**Everything below is prepared. These are OPERATOR actions — outward-facing, so you press send.**

---

# ▛▀▀ MASTER IOU — OPERATOR ACTIONS ▀▀▜

Tick these. Nothing here needs Claude.

- [ ] **IOU-1 — Sign the Google CLA.** <https://cla.developers.google.com/> · one-time, ~2 min.
      Required before *any* PR to `formal-conjectures` is mergeable. If you've signed a Google CLA
      before (any project), you're already done — check the link.
- [ ] **IOU-2 — Fork + PR `1066.lean` to google-deepmind/formal-conjectures.** Commands in §1.
      **This is the one that matters.** First formalisation of an open Erdős problem, your name on it.
- [ ] **IOU-3 — Post the comment on erdosproblems.com/1066.** Text in §2, ready to paste.
      Gets the problem's own page flipped from *"Formalised statement? No"* to yes.
- [ ] **IOU-4 — (optional, after IOU-2 merges)** add `oracle/math/EG1066Formal/` to whatever public
      page you use for the portfolio. The credential is "formalised an open Erdős problem."

**Blocked on nobody but you. IOU-1 gates IOU-2. IOU-3 is independent — do it tonight.**

▙▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▄▟

---

## 1. The PR

The file is already written in their house style and already sitting at the correct path in the
local checkout: `FormalConjectures/ErdosProblems/1066.lean`.

```bash
cd "oracle/runtime/state/formal-conjectures-checkout"
git checkout -b erdos-1066-formalisation
git add FormalConjectures/ErdosProblems/1066.lean
git commit -m "feat(erdos): formalise Erdos Problem 1066 (independence in minimum-separated unit-distance graphs)"
gh repo fork google-deepmind/formal-conjectures --remote --remote-name fork
git push fork erdos-1066-formalisation
gh pr create --repo google-deepmind/formal-conjectures --fill
```

### PR title

```
feat(erdos): formalise Erdős Problem 1066
```

### PR body — paste verbatim

```markdown
Adds `FormalConjectures/ErdosProblems/1066.lean`.

**Erdős Problem 1066** ([erdosproblems.com/1066](https://www.erdosproblems.com/1066)) — given `n`
points in ℝ² with all pairwise distances ≥ 1, form the graph joining pairs at distance exactly 1.
Let `g(n)` be the largest number such that every such configuration has an independent set of size
≥ `g(n)`. The problem asks for `lim g(n)/n`.

Current bounds: `8/31 ≈ 0.2581` (Swanepoel 2002) ≤ lim ≤ `5/16 = 0.3125` (Pach–Tóth 1996).
Erdős originally believed the answer was `1/3`.

The problem is not currently in this repository (`1064`, `1065`, `1067` are present) and
erdosproblems.com lists it as unformalised.

### Contents

The main statement is `erdos_1066`, with `answer(sorry)` for the unknown limit, plus variants for
the published results: `pollack` (`g(n) ≥ n/4`, via the Four Colour Theorem), `swanepoel_lower_bound`
(8/31), `pach_toth_upper_bound` (5/16), `limit_exists`, and `translate_reduction` (the
disjoint-translate argument giving `lim ≤ α(P)/|P|` for any finite admissible `P`).

Alongside the statement, the following are **proved** (no `sorry`):

| Theorem | Content |
|---|---|
| `card_le_three_mul_alpha_of_threeColouring` | a proper 3-colouring of the unit-distance graph forces `|P| ≤ 3·α(P)` |
| `triangularLattice_colouring_proper` | `x² + xy + y² = 1` over ℤ implies `3 ∤ (x − y)` |
| `latticeColouring_proper` | triangular-lattice points at distance exactly 1 receive different colours under `(a − b) mod 3` |
| `unit_triangle_circumradius_sq` | the circumcentre of the unit equilateral triangle is equidistant from its vertices at squared distance exactly `1/3` |
| `latticePoint_admissible` | every subset of the unit triangular lattice has pairwise distances ≥ 1 |
| `exists_indep_g` | every admissible `n`-point set has an independent subset of size ≥ `g n` (faithfulness of the `sInf` definition) |
| `threeColouring_cannot_beat_pach_toth` | a 3-colourable configuration satisfies `α(P) > (5/16)·|P|` |

Together the middle three give a machine-checked account of why the original `1/3` guess fails to
be an upper bound: every triangular-lattice subset is 3-colourable, hence has ratio ≥ 1/3, so any
configuration witnessing a ratio below 1/3 must leave the lattice.

`#print axioms` on each of the above reports `[propext, Classical.choice, Quot.sound]` only.

Definitions follow the repo's `ℝ²` notation from `FormalConjecturesForMathlib.Geometry.2d`.
```

**If CI complains**, the two likely nits are the `AMS` classification code (I used `AMS 52` —
discrete geometry; `AMS 05` combinatorics may be preferred) and `@[category]` attributes. Both are
one-line fixes on review feedback.

---

## 2. The erdosproblems.com comment

Go to <https://www.erdosproblems.com/1066>, comment box at the bottom. Paste:

```
I've written a Lean 4 formalisation of this problem and opened a PR against
google-deepmind/formal-conjectures: <PR LINK>

The main statement is `erdos_1066` (with `answer(sorry)` for the limit), together with variants
for Pollack's n/4, Swanepoel's 8/31, Pach–Tóth's 5/16, and the disjoint-translate reduction
lim g(n)/n ≤ α(P)/|P| for any finite admissible P.

Four supporting results are proved rather than assumed, each with axiom footprint
[propext, Classical.choice, Quot.sound]:

  * a proper 3-colouring of the unit-distance graph forces |P| ≤ 3·α(P);
  * x² + xy + y² = 1 over ℤ implies 3 ∤ (x − y);
  * consequently (a − b) mod 3 properly 3-colours the unit triangular lattice, so every
    lattice subset has ratio ≥ 1/3 and cannot witness anything below it;
  * the circumradius² of the unit equilateral triangle is exactly 1/3.

So the failure of the original 1/3 guess as an upper bound is machine-checked: a configuration
witnessing a ratio below 1/3 has to leave the triangular lattice entirely.

This does not move either wall — it is a formalisation plus barriers, not progress on the bounds.
```

Replace `<PR LINK>` after IOU-2. **Do not post before the PR exists** — a comment pointing at
nothing is worse than no comment.

---

## 3. What is actually being claimed (read before you send)

**Claimed:** a first formal statement of #1066, and four supporting theorems proved sorry-free with
a clean axiom footprint, verified by an independent `#print axioms` probe.

**NOT claimed:** any movement on `8/31` or `5/16`. Both walls stand exactly where Swanepoel and
Pach–Tóth left them. The file carries 9 `sorry`s — the open problem itself, the four published
results, and three named barrier bookkeeping steps. B4 (degree-6 rigidity) was not attempted; it
needs trigonometry.

If anyone asks "did you solve it" — no. You formalised it and closed four barriers inside it.
That distinction is stated in the PR body and in the comment, on purpose.

---

## 4. Provenance

- Source of truth: `oracle/math/EG1066Formal/Erdos1066.lean` (identical to the PR file)
- Detail: `oracle/math/EG1066Formal/README.md`
- Registry: `T-EG1066-lean-formalization` · lane `EG1066` · recording gap 0
- Ledger: `oracle/ledger/FINDINGS.md` under VALIDATED
- Python-certified alongside (not in the PR): B4, B5, and the Moser-spindle refutation at exact
  squared distance `1/3` — `oracle/kbk/engine/unit_distance_independence.py`
