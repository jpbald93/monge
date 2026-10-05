# SPIKE_REPORT — monge

**Item 17** of the Lean queue (batch 2, 2026-10-03). Monge's theorem for three circles
(the three external centres of similitude are collinear). Lean v4.33.1, project
`jack:~/monge`, library `Monge`, mathlib rev `v4.33.1`.

**Status: DONE — gate PASS** (full `lake build` 0 errors / 0 warnings; forbidden-token
grep empty; `#print axioms` shows only `propext, Classical.choice, Quot.sound`).

> **Warning honoured:** Mathlib's `Geometry/Euclidean/MongePoint.lean` is the *Monge point
> of a tetrahedron/simplex* — a **different** theorem. It is **not** imported or used here.

---

## 1. Prior art (Step 0)

Searched Mathlib source, `docs/100.yaml`/`1000.yaml`, `gh search code/prs/repos`,
AFP, Coq/Rocq, Mizar, web.

* **Mathlib**: no statement of Monge's theorem for circles. `gh search code "monge" language:lean`
  returns only (a) the tetrahedron `MongePoint.lean`, and (b) `TauCetiProject/TauCeti`
  `MeasureTheory/OptimalTransport/Monge.lean` (the *Monge optimal-transport problem* — unrelated).
  No centre-of-similitude / Monge-line API exists (`Geometry/Euclidean/Circle` etc. have no such notion).
* **Open Mathlib PR #43646** (2026-09-28): centroid/circumcentre/Monge **point of a simplex** —
  still the tetrahedron theorem, unrelated, unmerged.
* **Isabelle AFP / HOL Light / Coq / Mizar**: no hits for Monge's three-circle theorem.
* `gh search repos "monge theorem"` → only interactive visualisation apps
  (miapuffia/Monges-Theorem, andrewlidong/monges-theorem, Mitko-Kerezov/Monges-Theorem),
  no formalisation.

**Conclusion**: no complete formal proof of Monge's circle theorem exists in Lean or any
other proof assistant found. Proceeding with a fresh coordinate proof.

## 2. Informal check (Mathlib hygiene)

Python on the VM, `code/check_monge.py` (never on jack):

| check | result |
|---|---|
| 2000 random configurations over `ℚ` (distinct radii), `det3(S12,S23,S31)==0` | **0 failures** |
| **negative control**: arbitrary points on the three lines `O_iO_j` | 14/2000 accidentally collinear ⇒ collinearity is *not* automatic; the external-centre formula is what forces it |
| non-vacuity example: centres `(0,0),(4,0),(0,3)`, radii `1,2,3` | `S12=(-4,0)`, `S23=(12,-6)`, `S31=(0,-3/2)`, `det3=0` |

## 3. What was proved (exact Lean statements, copied from source)

All in `namespace Monge`, over `variable {K : Type*} [Field K]` (`Monge/Basic.lean`).

```lean
-- Monge/Basic.lean:42
def ext (O₁ O₂ : K × K) (r₁ r₂ : K) : K × K :=
  ((r₁ * O₂.1 - r₂ * O₁.1) / (r₁ - r₂), (r₁ * O₂.2 - r₂ * O₁.2) / (r₁ - r₂))

-- Monge/Basic.lean:48
def det3 (A B C : K × K) : K :=
  (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)

-- Monge/Basic.lean:55  **headline**
theorem monge (O₁ O₂ O₃ : K × K) (r₁ r₂ r₃ : K)
    (h12 : r₁ ≠ r₂) (h23 : r₂ ≠ r₃) (h31 : r₃ ≠ r₁) :
    det3 (ext O₁ O₂ r₁ r₂) (ext O₂ O₃ r₂ r₃) (ext O₃ O₁ r₃ r₁) = 0

-- Monge/Basic.lean:71  non-vacuity example
theorem monge_example :
    det3 (ext ((0:ℚ),(0:ℚ)) ((4:ℚ),(0:ℚ)) 1 2)
         (ext ((4:ℚ),(0:ℚ)) ((0:ℚ),(3:ℚ)) 2 3)
         (ext ((0:ℚ),(3:ℚ)) ((0:ℚ),(0:ℚ)) 3 1) = 0

-- Monge/Basic.lean:78  the example is non-degenerate
theorem monge_example_values :
    ext ((0:ℚ),(0:ℚ)) ((4:ℚ),(0:ℚ)) 1 2 = ((-4:ℚ), 0)
    ∧ ext ((4:ℚ),(0:ℚ)) ((0:ℚ),(3:ℚ)) 2 3 = ((12:ℚ), -6)
    ∧ ext ((0:ℚ),(3:ℚ)) ((0:ℚ),(0:ℚ)) 3 1 = ((0:ℚ), -3/2)
```

`monge` is proved by `unfold det3 ext; field_simp; ring` (the only side conditions are the
three nonzero denominators from distinct radii).

## 4. Hypotheses — meaning and exceptional cases

* `ext O₁ O₂ r₁ r₂` is the external centre of similitude of the two circles: the point of
  line `O₁O₂` dividing it externally in the ratio `r₁ : r₂`.
* **Distinct radii per pair** (`r₁≠r₂`, `r₂≠r₃`, `r₃≠r₁`) are exactly the denominators being
  nonzero — needed so each external centre is a finite point. If `r₁ = r₂` the two circles
  are *equal-radius* and the external centre is a point at infinity (the Monge line becomes
  a line through the remaining finite centre parallel to `O₁O₂`); this limit case is **not**
  formalised.
* **Non-coincident centres** are *not* required for the algebraic identity: the proof is a
  polynomial/rational identity valid for all `O_i` and all distinct `r_i`. When two centres
  coincide the geometric interpretation of "the line `O_iO_j`" degenerates, but the
  collinearity statement still holds. We therefore state the theorem without a centres
  hypothesis and name this honestly.
* Over `ℝ` (`K = ℝ`) this is the classical statement; the proof is field-generic.

## 5. Gate output (pasted)

```
✔ [3006/3008] Built Monge.Basic (1.4s)
✔ [3007/3008] Built Monge (1.1s)
Build completed successfully (3008 jobs).
EXIT 0
```
(no `warning` lines in `build.log`)

Forbidden-token grep over `Monge Monge.lean` (sorry/admit/native_decide/axiom/#eval/
run_cmd/set_option/macro/elab/syntax/notation/import Lean): **empty**.

`lake env lean scratch/Ax.lean`:
```
'Monge.monge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Monge.monge_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'Monge.monge_example_values' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. What is NOT done

* No formalisation of the *internal* centre of similitude, of tangents to circles, or of the
  "tangent lines concur" equivalent phrasing of Monge's theorem.
* No geometry of circles is used: the statement is purely the algebraic collinearity
  criterion applied to the explicit formula. (This is the requested coordinate proof.)
* The equal-radius / point-at-infinity limit case (`r_i = r_j`) is excluded by hypotheses.
* Not pushed to GitHub.
