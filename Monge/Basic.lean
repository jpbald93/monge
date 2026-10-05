import Mathlib.Tactic

/-!
# Monge's theorem for three circles (coordinate form)

We work in the coordinate plane `K × K` over a field `K` (think `K = ℝ`).

For two circles with centres `O₁, O₂` and radii `r₁, r₂`, the **external centre of
similitude** is the point of the line `O₁O₂` dividing it externally in the ratio
`r₁ : r₂`, i.e.

`S₁₂ = (r₁ · O₂ − r₂ · O₁) / (r₁ − r₂)`.

**Monge's theorem.** For three circles whose radii are pairwise distinct, the three
external centres of similitude `S₁₂`, `S₂₃`, `S₃₁` are collinear.

We use the standard algebraic collinearity criterion: the signed double area
`det3 A B C` of the triangle `ABC` vanishes.

This is *not* the Monge point of a tetrahedron/simplex
(`Mathlib.Geometry.Euclidean.MongePoint`); it is a genuinely different theorem.
-/

namespace Monge

variable {K : Type*} [Field K]

/-- External centre of similitude of the circles with centres `O₁, O₂` and radii
`r₁, r₂`, as a point of the coordinate plane `K × K`:
`S = (r₁ · O₂ − r₂ · O₁) / (r₁ − r₂)` (componentwise). -/
def ext (O₁ O₂ : K × K) (r₁ r₂ : K) : K × K :=
  ((r₁ * O₂.1 - r₂ * O₁.1) / (r₁ - r₂), (r₁ * O₂.2 - r₂ * O₁.2) / (r₁ - r₂))

/-- Signed double area of the triangle `ABC`: `(B−A) × (C−A)`. It vanishes exactly
when `A, B, C` are collinear. -/
def det3 (A B C : K × K) : K :=
  (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)

/-- **Monge's theorem** (coordinate form): if the radii are pairwise distinct
(`r₁ ≠ r₂`, `r₂ ≠ r₃`, `r₃ ≠ r₁`), the three external centres of similitude are
collinear. -/
theorem monge (O₁ O₂ O₃ : K × K) (r₁ r₂ r₃ : K)
    (h12 : r₁ ≠ r₂) (h23 : r₂ ≠ r₃) (h31 : r₃ ≠ r₁) :
    det3 (ext O₁ O₂ r₁ r₂) (ext O₂ O₃ r₂ r₃) (ext O₃ O₁ r₃ r₁) = 0 := by
  have h12' : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr h12
  have h23' : r₂ - r₃ ≠ 0 := sub_ne_zero.mpr h23
  have h31' : r₃ - r₁ ≠ 0 := sub_ne_zero.mpr h31
  unfold det3 ext
  field_simp
  ring

/-- Non-vacuity: three concrete circles over `ℚ`, centres `(0,0), (4,0), (0,3)` and
radii `1, 2, 3`; their external centres of similitude are collinear. -/
theorem monge_example :
    det3 (ext ((0 : ℚ), (0 : ℚ)) ((4 : ℚ), (0 : ℚ)) 1 2)
         (ext ((4 : ℚ), (0 : ℚ)) ((0 : ℚ), (3 : ℚ)) 2 3)
         (ext ((0 : ℚ), (3 : ℚ)) ((0 : ℚ), (0 : ℚ)) 3 1) = 0 := by
  norm_num [det3, ext]

/-- The example is non-degenerate: `S₁₂ = (−4, 0)`, `S₂₃ = (12, −6)`, `S₃₁ = (0, −3/2)`. -/
theorem monge_example_values :
    ext ((0 : ℚ), (0 : ℚ)) ((4 : ℚ), (0 : ℚ)) 1 2 = ((-4 : ℚ), 0)
    ∧ ext ((4 : ℚ), (0 : ℚ)) ((0 : ℚ), (3 : ℚ)) 2 3 = ((12 : ℚ), -6)
    ∧ ext ((0 : ℚ), (3 : ℚ)) ((0 : ℚ), (0 : ℚ)) 3 1 = ((0 : ℚ), -3 / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [ext]

end Monge
