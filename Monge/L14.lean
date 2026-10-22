import Monge.Bridge

/-!
# Layer 14: Mathlib-only restatement and a witness for Monge's theorem

`l14_monge` mentions only Mathlib notions. The external centre of similitude `S₁₂` of the
circles `(O₁, r₁)`, `(O₂, r₂)` is given by its **defining property**
`r₁ • (O₂ -ᵥ S₁₂) = r₂ • (O₁ -ᵥ S₁₂)`: the vectors from `S₁₂` to the two centres are in the
ratio of the radii (for `r₁ ≠ 0` this says that the homothety of centre `S₁₂` and ratio `r₂ / r₁`
sends `O₁` to `O₂`, see `l14_monge_homothety`). For `r₁ ≠ r₂` this point exists and is unique
(`l14b_ext_unique`). The conclusion is Mathlib's `Collinear`.

`l14w_monge` is the example of the paper over `ℚ`: centres `(0,0)`, `(4,0)`, `(0,3)` (not
collinear) and radii `1, 2, 3`; the centres of similitude `(-4, 0)`, `(12, -6)`, `(0, -3/2)` satisfy
the defining property and are pairwise distinct.
-/

namespace Monge

variable {K : Type*} [Field K]

/-- **Bridge.** A point with the defining property of the centre of similitude is `ext`. -/
theorem l14b_ext_unique {O₁ O₂ S : K × K} {r₁ r₂ : K} (h12 : r₁ ≠ r₂)
    (h : r₁ • (O₂ -ᵥ S) = r₂ • (O₁ -ᵥ S)) : S = ext O₁ O₂ r₁ r₂ := by
  have h' : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr h12
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [vsub_eq_sub, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] at e1 e2
  refine Prod.ext ?_ ?_
  · simp only [ext]; field_simp; linear_combination -e1
  · simp only [ext]; field_simp; linear_combination -e2

/-- **Monge's theorem**, Mathlib-only statement: the three external centres of similitude
(by their defining property) of three circles with pairwise distinct radii are collinear. -/
theorem l14_monge (O₁ O₂ O₃ S₁₂ S₂₃ S₃₁ : K × K) (r₁ r₂ r₃ : K)
    (h12 : r₁ ≠ r₂) (h23 : r₂ ≠ r₃) (h31 : r₃ ≠ r₁)
    (hS₁₂ : r₁ • (O₂ -ᵥ S₁₂) = r₂ • (O₁ -ᵥ S₁₂))
    (hS₂₃ : r₂ • (O₃ -ᵥ S₂₃) = r₃ • (O₂ -ᵥ S₂₃))
    (hS₃₁ : r₃ • (O₁ -ᵥ S₃₁) = r₁ • (O₃ -ᵥ S₃₁)) :
    Collinear K ({S₁₂, S₂₃, S₃₁} : Set (K × K)) := by
  rw [l14b_ext_unique h12 hS₁₂, l14b_ext_unique h23 hS₂₃, l14b_ext_unique h31 hS₃₁,
    ← det3_eq_zero_iff_collinear]
  exact monge O₁ O₂ O₃ r₁ r₂ r₃ h12 h23 h31

/-- **Monge's theorem**, homothety form (Mathlib-only): for nonzero radii, `S₁₂` is the centre
of the homothety of ratio `r₂ / r₁` sending `O₁` to `O₂`, and likewise for `S₂₃`, `S₃₁`. -/
theorem l14_monge_homothety (O₁ O₂ O₃ S₁₂ S₂₃ S₃₁ : K × K) (r₁ r₂ r₃ : K)
    (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0)
    (h12 : r₁ ≠ r₂) (h23 : r₂ ≠ r₃) (h31 : r₃ ≠ r₁)
    (hS₁₂ : AffineMap.homothety S₁₂ (r₂ / r₁) O₁ = O₂)
    (hS₂₃ : AffineMap.homothety S₂₃ (r₃ / r₂) O₂ = O₃)
    (hS₃₁ : AffineMap.homothety S₃₁ (r₁ / r₃) O₃ = O₁) :
    Collinear K ({S₁₂, S₂₃, S₃₁} : Set (K × K)) := by
  have key : ∀ {P Q S : K × K} {a b : K}, a ≠ 0 →
      AffineMap.homothety S (b / a) P = Q → a • (Q -ᵥ S) = b • (P -ᵥ S) := by
    intro P Q S a b ha h
    rw [← h, AffineMap.homothety_apply, vadd_vsub, smul_smul, mul_div_cancel₀ _ ha]
  exact l14_monge O₁ O₂ O₃ S₁₂ S₂₃ S₃₁ r₁ r₂ r₃ h12 h23 h31 (key h₁ hS₁₂) (key h₂ hS₂₃)
    (key h₃ hS₃₁)

/-- Witness for `l14_monge` over `ℚ`. -/
theorem l14w_monge :
    ((1 : ℚ) ≠ 2 ∧ (2 : ℚ) ≠ 3 ∧ (3 : ℚ) ≠ 1) ∧
    (1 : ℚ) • (((4 : ℚ), (0 : ℚ)) -ᵥ ((-4 : ℚ), (0 : ℚ))) =
      (2 : ℚ) • (((0 : ℚ), (0 : ℚ)) -ᵥ ((-4 : ℚ), (0 : ℚ))) ∧
    (2 : ℚ) • (((0 : ℚ), (3 : ℚ)) -ᵥ ((12 : ℚ), (-6 : ℚ))) =
      (3 : ℚ) • (((4 : ℚ), (0 : ℚ)) -ᵥ ((12 : ℚ), (-6 : ℚ))) ∧
    (3 : ℚ) • (((0 : ℚ), (0 : ℚ)) -ᵥ ((0 : ℚ), (-3 / 2 : ℚ))) =
      (1 : ℚ) • (((0 : ℚ), (3 : ℚ)) -ᵥ ((0 : ℚ), (-3 / 2 : ℚ))) ∧
    ¬ Collinear ℚ ({((0 : ℚ), (0 : ℚ)), ((4 : ℚ), (0 : ℚ)), ((0 : ℚ), (3 : ℚ))} :
      Set (ℚ × ℚ)) ∧
    (((-4 : ℚ), (0 : ℚ)) ≠ ((12 : ℚ), (-6 : ℚ)) ∧ ((12 : ℚ), (-6 : ℚ)) ≠ ((0 : ℚ), (-3 / 2 : ℚ)) ∧
      ((0 : ℚ), (-3 / 2 : ℚ)) ≠ ((-4 : ℚ), (0 : ℚ))) ∧
    Collinear ℚ ({((-4 : ℚ), (0 : ℚ)), ((12 : ℚ), (-6 : ℚ)), ((0 : ℚ), (-3 / 2 : ℚ))} :
      Set (ℚ × ℚ)) := by
  have hne : (1 : ℚ) ≠ 2 ∧ (2 : ℚ) ≠ 3 ∧ (3 : ℚ) ≠ 1 := by norm_num
  have p1 : (1 : ℚ) • (((4 : ℚ), (0 : ℚ)) -ᵥ ((-4 : ℚ), (0 : ℚ))) =
      (2 : ℚ) • (((0 : ℚ), (0 : ℚ)) -ᵥ ((-4 : ℚ), (0 : ℚ))) := by
    simp only [vsub_eq_sub, Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul]; norm_num
  have p2 : (2 : ℚ) • (((0 : ℚ), (3 : ℚ)) -ᵥ ((12 : ℚ), (-6 : ℚ))) =
      (3 : ℚ) • (((4 : ℚ), (0 : ℚ)) -ᵥ ((12 : ℚ), (-6 : ℚ))) := by
    simp only [vsub_eq_sub, Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul]; norm_num
  have p3 : (3 : ℚ) • (((0 : ℚ), (0 : ℚ)) -ᵥ ((0 : ℚ), (-3 / 2 : ℚ))) =
      (1 : ℚ) • (((0 : ℚ), (3 : ℚ)) -ᵥ ((0 : ℚ), (-3 / 2 : ℚ))) := by
    simp only [vsub_eq_sub, Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul]; norm_num
  refine ⟨hne, p1, p2, p3, ?_, ?_, l14_monge _ _ _ _ _ _ 1 2 3 hne.1 hne.2.1 hne.2.2 p1 p2 p3⟩
  · rw [← det3_eq_zero_iff_collinear]; norm_num [det3]
  · refine ⟨?_, ?_, ?_⟩ <;> simp

end Monge
