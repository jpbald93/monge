import Monge.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Definition bridges

The two local definitions of `Monge.Basic`, tied to the standard Mathlib notions:

* `det3_eq_zero_iff_collinear` : `det3 A B C = 0` is exactly Mathlib's `Collinear K {A, B, C}`
  in the coordinate plane `K × K`;
* `ext_eq_lineMap_homothety` : `ext O₁ O₂ r₁ r₂` lies on the line `O₁O₂` (`AffineMap.lineMap`) and is
  the centre of the homothety (`AffineMap.homothety`) of ratio `r₂ / r₁` sending `O₁` to `O₂` —
  i.e. it is the centre of similitude of the two circles.
-/

namespace Monge

variable {K : Type*} [Field K]

/-- **Bridge for `det3`.** The signed double area vanishes iff the three points are collinear
in Mathlib's sense. -/
theorem det3_eq_zero_iff_collinear (A B C : K × K) : det3 A B C = 0 ↔
    Collinear K ({A, B, C} : Set (K × K)) := by
  rw [collinear_iff_of_mem (p₀ := A) (by simp)]
  constructor
  · intro h
    unfold det3 at h
    by_cases hAB : B = A
    · subst hAB
      refine ⟨C - B, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    · refine ⟨B - A, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · by_cases h1 : B.1 - A.1 = 0
        · have h2 : B.2 - A.2 ≠ 0 := by
            intro h2; apply hAB
            exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
          refine ⟨(p.2 - A.2) / (B.2 - A.2), ?_⟩
          refine Prod.ext ?_ ?_
          · simp only [vadd_eq_add, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
            have hp1 : p.1 - A.1 = 0 := by
              rw [h1] at h
              have h' : (B.2 - A.2) * (p.1 - A.1) = 0 := by linear_combination (-1 : K) * h
              exact (mul_eq_zero.mp h').resolve_left h2
            rw [sub_eq_zero.mp h1]
            linear_combination hp1
          · simp only [vadd_eq_add, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
            field_simp
            ring
        · refine ⟨(p.1 - A.1) / (B.1 - A.1), ?_⟩
          refine Prod.ext ?_ ?_
          · simp only [vadd_eq_add, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
            field_simp
            ring
          · simp only [vadd_eq_add, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
            field_simp
            linear_combination h
  · rintro ⟨v, hv⟩
    obtain ⟨s, hs⟩ := hv B (by simp)
    obtain ⟨t, ht⟩ := hv C (by simp)
    have hB1 : B.1 = s * v.1 + A.1 := by simpa using congrArg Prod.fst hs
    have hB2 : B.2 = s * v.2 + A.2 := by simpa using congrArg Prod.snd hs
    have hC1 : C.1 = t * v.1 + A.1 := by simpa using congrArg Prod.fst ht
    have hC2 : C.2 = t * v.2 + A.2 := by simpa using congrArg Prod.snd ht
    unfold det3
    rw [hB1, hB2, hC1, hC2]
    ring

variable (O₁ O₂ : K × K) {r₁ r₂ : K}

/-- **Bridge for `ext`.** For `r₁ ≠ 0` and `r₁ ≠ r₂`, the point `ext O₁ O₂ r₁ r₂` lies on the
line `O₁O₂` (it is `lineMap O₁ O₂ (r₁ / (r₁ - r₂))`) and is the centre of the homothety of
ratio `r₂ / r₁` that sends the centre `O₁` to the centre `O₂` (hence the circle of radius `r₁`
onto the circle of radius `r₂`). -/
theorem ext_eq_lineMap_homothety (h₁ : r₁ ≠ 0) (h12 : r₁ ≠ r₂) : ext O₁ O₂ r₁ r₂ =
    AffineMap.lineMap O₁ O₂ (r₁ / (r₁ - r₂)) ∧
      AffineMap.homothety (ext O₁ O₂ r₁ r₂) (r₂ / r₁) O₁ = O₂ := by
  have h12' : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr h12
  constructor
  · rw [AffineMap.lineMap_apply]
    refine Prod.ext ?_ ?_
    · simp only [ext, vadd_eq_add, vsub_eq_sub, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      field_simp
      ring
    · simp only [ext, vadd_eq_add, vsub_eq_sub, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      field_simp
      ring
  · rw [AffineMap.homothety_apply]
    refine Prod.ext ?_ ?_
    · simp only [ext, vadd_eq_add, vsub_eq_sub, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      field_simp
      ring
    · simp only [ext, vadd_eq_add, vsub_eq_sub, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      field_simp
      ring

end Monge
