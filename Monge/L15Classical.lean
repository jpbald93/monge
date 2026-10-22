import Monge.Basic
import Monge.Bridge
import Monge.L14
import Mathlib

/-!
# Layer 15: independent classical statements

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.

Comparison of the writer statements `classical_A2_*` vs. the Monge library.
-/

open EuclideanGeometry

noncomputable section

namespace Monge.Classical

/-! Writer's definitions, verbatim. -/

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsExtSimCenter (s t : Sphere Plane) (E : Plane) : Prop :=
  AffineMap.homothety E (t.radius / s.radius) '' Metric.sphere s.center s.radius =
    Metric.sphere t.center t.radius

def IsIntSimCenter (s t : Sphere Plane) (I : Plane) : Prop :=
  Wbtw ℝ s.center I t.center ∧ t.radius * dist s.center I = s.radius * dist I t.center

/-! Writer's statements, verbatim, packaged as `Prop`s. -/

def classical_A2_obligation_ext : Prop :=
  ∀ (s t : Sphere Plane) (_hs : 0 < s.radius) (_ht : 0 < t.radius)
    (_hc : s.center ≠ t.center) (_hr : s.radius ≠ t.radius),
    ∃! E : Plane, IsExtSimCenter s t E

def classical_A2_obligation_int : Prop :=
  ∀ (s t : Sphere Plane) (_hs : 0 < s.radius) (_ht : 0 < t.radius)
    (_hc : s.center ≠ t.center),
    ∃! I : Plane, IsIntSimCenter s t I

def classical_A2_a : Prop :=
  ∀ (s₁ s₂ s₃ : Sphere Plane)
    (_h₁ : 0 < s₁.radius) (_h₂ : 0 < s₂.radius) (_h₃ : 0 < s₃.radius)
    (_hc₁₂ : s₁.center ≠ s₂.center) (_hc₂₃ : s₂.center ≠ s₃.center)
    (_hc₁₃ : s₁.center ≠ s₃.center)
    (_hr₁₂ : s₁.radius ≠ s₂.radius) (_hr₂₃ : s₂.radius ≠ s₃.radius)
    (_hr₁₃ : s₁.radius ≠ s₃.radius)
    (E₁₂ E₂₃ E₁₃ : Plane)
    (_hE₁₂ : IsExtSimCenter s₁ s₂ E₁₂) (_hE₂₃ : IsExtSimCenter s₂ s₃ E₂₃)
    (_hE₁₃ : IsExtSimCenter s₁ s₃ E₁₃),
    Collinear ℝ ({E₁₂, E₂₃, E₁₃} : Set Plane)

def classical_A2_b : Prop :=
  ∀ (s₁ s₂ s₃ : Sphere Plane)
    (_h₁ : 0 < s₁.radius) (_h₂ : 0 < s₂.radius) (_h₃ : 0 < s₃.radius)
    (_hc₁₂ : s₁.center ≠ s₂.center) (_hc₂₃ : s₂.center ≠ s₃.center)
    (_hc₁₃ : s₁.center ≠ s₃.center)
    (_hr₁₂ : s₁.radius ≠ s₂.radius) (_hr₂₃ : s₂.radius ≠ s₃.radius)
    (_hr₁₃ : s₁.radius ≠ s₃.radius)
    (E₁₂ I₂₃ I₁₃ : Plane)
    (_hE₁₂ : IsExtSimCenter s₁ s₂ E₁₂) (_hI₂₃ : IsIntSimCenter s₂ s₃ I₂₃)
    (_hI₁₃ : IsIntSimCenter s₁ s₃ I₁₃),
    Collinear ℝ ({E₁₂, I₂₃, I₁₃} : Set Plane)

/-! ## Glue -/

/-- Collinearity is preserved by linear maps. -/
lemma collinear_image {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) {s : Set V} (h : Collinear ℝ s) : Collinear ℝ (f '' s) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨p₀, v, hv⟩ := h
  refine ⟨f p₀, f v, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨r, rfl⟩ := hv p hp
  exact ⟨r, by simp [vadd_eq_add]⟩

/-- Coordinate plane `ℝ × ℝ` into the Euclidean plane. -/
def ψ : (ℝ × ℝ) →ₗ[ℝ] Plane where
  toFun p := p.1 • EuclideanSpace.single 0 1 + p.2 • EuclideanSpace.single 1 1
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c p := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul,
    RingHom.id_apply, smul_add]

lemma ψ_apply0 (p : ℝ × ℝ) : ψ p 0 = p.1 := by simp [ψ]
lemma ψ_apply1 (p : ℝ × ℝ) : ψ p 1 = p.2 := by simp [ψ]

/-- Coordinates of a point. -/
def φ (x : Plane) : ℝ × ℝ := (x 0, x 1)

/-- A point given by the external-centre equation is the library's `Monge.ext`. -/
lemma eq_ψ_ext {a b : ℝ} {X Y E : Plane} (hab : a ≠ b) (h : (a - b) • E = a • Y - b • X) :
    E = ψ (Monge.ext (φ X) (φ Y) a b) := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  ext i
  fin_cases i
  · have := congrFun (congrArg (fun z : Plane => (z : Fin 2 → ℝ)) h) 0
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at this
    simp only [Fin.zero_eta, Fin.isValue, ψ_apply0, Monge.ext, φ]
    field_simp
    linear_combination this
  · have := congrFun (congrArg (fun z : Plane => (z : Fin 2 → ℝ)) h) 1
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at this
    simp only [Fin.mk_one, Fin.isValue, ψ_apply1, Monge.ext, φ]
    field_simp
    linear_combination this

/-- From the writer's homothety definition: `(r_s - r_t) • E = r_s • O_t - r_t • O_s`. -/
lemma ext_eq_of_isExt (s t : Sphere Plane) (hs : 0 < s.radius) (ht : 0 < t.radius)
    (E : Plane) (hE : IsExtSimCenter s t E) :
    (s.radius - t.radius) • E = s.radius • t.center - t.radius • s.center := by
  set k := t.radius / s.radius with hk
  set u : Plane := EuclideanSpace.single 0 1
  have hu : ‖u‖ = 1 := by simp [u]
  have hmem : ∀ x : Plane, ‖x - s.center‖ = s.radius →
      ‖AffineMap.homothety E k x - t.center‖ = t.radius := by
    intro x hx
    have : AffineMap.homothety E k x ∈ Metric.sphere t.center t.radius := by
      rw [← hE]; exact Set.mem_image_of_mem _ (by rw [Metric.mem_sphere, dist_eq_norm]; exact hx)
    rwa [Metric.mem_sphere, dist_eq_norm] at this
  have hsr : s.radius ≠ 0 := hs.ne'
  have hkr : k * s.radius = t.radius := by rw [hk]; field_simp
  set a : Plane := k • (s.center - E) + E - t.center with ha
  have hp := hmem (s.center + s.radius • u) (by simp [norm_smul, hu, abs_of_pos hs])
  have hm := hmem (s.center - s.radius • u) (by simp [norm_smul, hu, abs_of_pos hs])
  rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] at hp hm
  have ep : k • (s.center + s.radius • u - E) + E - t.center = a + t.radius • u := by
    rw [ha, ← hkr, mul_smul]; simp only [smul_add, smul_sub]; abel
  have em : k • (s.center - s.radius • u - E) + E - t.center = a - t.radius • u := by
    rw [ha, ← hkr, mul_smul]; simp only [smul_add, smul_sub]; abel
  rw [ep] at hp; rw [em] at hm
  have h1 := norm_add_sq_real a (t.radius • u)
  have h2 := norm_sub_sq_real a (t.radius • u)
  rw [hp] at h1; rw [hm] at h2
  have hn : ‖t.radius • u‖ = t.radius := by simp [norm_smul, hu, abs_of_pos ht]
  rw [hn] at h1 h2
  have ha0 : ‖a‖ ^ 2 = 0 := by nlinarith
  have ha0' : a = 0 := by simpa using ha0
  have : k • (s.center - E) + E = t.center := by rw [← sub_eq_zero, ← ha]; exact ha0'
  have h3 : s.radius • (k • (s.center - E) + E) = s.radius • t.center := by rw [this]
  rw [smul_add, smul_smul, mul_comm, hkr, smul_sub] at h3
  rw [← h3]; simp only [sub_smul]; abel

/-- From the writer's internal-centre definition: `(r_s + r_t) • I = r_t • O_s + r_s • O_t`. -/
lemma int_eq_of_isInt (s t : Sphere Plane) (hs : 0 < s.radius) (ht : 0 < t.radius)
    (hc : s.center ≠ t.center) (I : Plane) (hI : IsIntSimCenter s t I) :
    (s.radius + t.radius) • I = t.radius • s.center + s.radius • t.center := by
  obtain ⟨⟨μ, ⟨hμ0, hμ1⟩, rfl⟩, hd⟩ := hI
  rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hμ0, abs_of_nonneg (by linarith)] at hd
  have hdist : dist s.center t.center ≠ 0 := dist_ne_zero.mpr hc
  have hμ : μ * (s.radius + t.radius) = s.radius := by
    have : (t.radius * μ - s.radius * (1 - μ)) * dist s.center t.center = 0 := by
      linear_combination hd
    have := (mul_eq_zero.mp this).resolve_right hdist
    linear_combination this
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_add, smul_smul, mul_comm, hμ,
    smul_sub, add_smul]
  abel

/-! ## Comparisons -/

/-- (E) A2(a), from `Monge.monge` and `Monge.det3_eq_zero_iff_collinear`. -/
theorem cov_A2_a : classical_A2_a := by
  intro s₁ s₂ s₃ h₁ h₂ h₃ _ _ _ hr₁₂ hr₂₃ hr₁₃ E₁₂ E₂₃ E₁₃ hE₁₂ hE₂₃ hE₁₃
  have e₁₂ := eq_ψ_ext hr₁₂ (ext_eq_of_isExt s₁ s₂ h₁ h₂ E₁₂ hE₁₂)
  have e₂₃ := eq_ψ_ext hr₂₃ (ext_eq_of_isExt s₂ s₃ h₂ h₃ E₂₃ hE₂₃)
  have e₁₃ := eq_ψ_ext (Ne.symm hr₁₃) (a := s₃.radius) (b := s₁.radius)
    (X := s₃.center) (Y := s₁.center) (E := E₁₃) (by
      have := ext_eq_of_isExt s₁ s₃ h₁ h₃ E₁₃ hE₁₃
      rw [← neg_sub, neg_smul, this]; abel)
  have hcol := (Monge.det3_eq_zero_iff_collinear _ _ _).mp
    (Monge.monge (φ s₁.center) (φ s₂.center) (φ s₃.center) s₁.radius s₂.radius s₃.radius
      hr₁₂ hr₂₃ (Ne.symm hr₁₃))
  have := collinear_image ψ hcol
  simp only [Set.image_insert_eq, Set.image_singleton] at this
  rwa [e₁₂, e₂₃, e₁₃]

/-- (E) A2(b), from `Monge.monge` with the third radius negated (the instantiation described
in the paper, Section Monge). -/
theorem cov_A2_b : classical_A2_b := by
  intro s₁ s₂ s₃ h₁ h₂ h₃ _ hc₂₃ hc₁₃ hr₁₂ _ _ E₁₂ I₂₃ I₁₃ hE₁₂ hI₂₃ hI₁₃
  have e₁₂ := eq_ψ_ext hr₁₂ (ext_eq_of_isExt s₁ s₂ h₁ h₂ E₁₂ hE₁₂)
  have e₂₃ := eq_ψ_ext (a := s₂.radius) (b := -s₃.radius) (X := s₂.center) (Y := s₃.center)
    (E := I₂₃) (by intro h; linarith) (by
      have := int_eq_of_isInt s₂ s₃ h₂ h₃ hc₂₃ I₂₃ hI₂₃
      rw [sub_neg_eq_add, this, neg_smul]; abel)
  have e₁₃ := eq_ψ_ext (a := -s₃.radius) (b := s₁.radius) (X := s₃.center) (Y := s₁.center)
    (E := I₁₃) (by intro h; linarith) (by
      have := int_eq_of_isInt s₁ s₃ h₁ h₃ hc₁₃ I₁₃ hI₁₃
      rw [show -s₃.radius - s₁.radius = -(s₁.radius + s₃.radius) by ring, neg_smul, this,
        neg_smul]; abel)
  have hcol := (Monge.det3_eq_zero_iff_collinear _ _ _).mp
    (Monge.monge (φ s₁.center) (φ s₂.center) (φ s₃.center) s₁.radius s₂.radius (-s₃.radius)
      hr₁₂ (by intro h; linarith) (by intro h; linarith))
  have := collinear_image ψ hcol
  simp only [Set.image_insert_eq, Set.image_singleton] at this
  rwa [e₁₂, e₂₃, e₁₃]

/-- (O, NEW PROOF) existence and uniqueness of the external centre (writer's obligation). -/
theorem cov_A2_obligation_ext : classical_A2_obligation_ext := by
  intro s t hs ht _ hr
  have hd : s.radius - t.radius ≠ 0 := sub_ne_zero.mpr hr
  set E : Plane := (s.radius - t.radius)⁻¹ • (s.radius • t.center - t.radius • s.center) with hE
  have hEeq : (s.radius - t.radius) • E = s.radius • t.center - t.radius • s.center := by
    rw [hE, smul_smul, mul_inv_cancel₀ hd, one_smul]
  set k := t.radius / s.radius with hk
  have hk0 : 0 < k := div_pos ht hs
  have hkr : k * s.radius = t.radius := by rw [hk]; field_simp
  -- the homothety sends `O_s` to `O_t`
  have hc : k • (s.center - E) + E = t.center := by
    have h3 : s.radius • (k • (s.center - E) + E) = s.radius • t.center := by
      rw [smul_add, smul_smul, mul_comm, hkr, smul_sub]
      have : s.radius • E = (s.radius - t.radius) • E + t.radius • E := by rw [sub_smul]; abel
      rw [this, hEeq]; abel
    exact smul_right_injective _ hs.ne' h3
  have hmap : ∀ x, AffineMap.homothety E k x - t.center = k • (x - s.center) := by
    intro x
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, ← hc, smul_sub, smul_sub, smul_sub]; abel
  refine ⟨E, ?_, fun E' hE' => ?_⟩
  · ext y
    simp only [Set.mem_image, Metric.mem_sphere, dist_eq_norm]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hmap, norm_smul, Real.norm_eq_abs, abs_of_pos hk0, hx, hkr]
    · intro hy
      refine ⟨s.center + k⁻¹ • (y - t.center), ?_, ?_⟩
      · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0), hy,
          ← hkr]
        field_simp
      · rw [← sub_eq_zero, show AffineMap.homothety E k (s.center + k⁻¹ • (y - t.center)) - y =
          (AffineMap.homothety E k (s.center + k⁻¹ • (y - t.center)) - t.center) - (y - t.center)
          by abel, hmap, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hk0.ne', one_smul, sub_self]
  · have h' := ext_eq_of_isExt s t hs ht E' hE'
    rw [← hEeq] at h'
    exact smul_right_injective _ hd h'

/-- (O, NEW PROOF) existence and uniqueness of the internal centre (writer's obligation). -/
theorem cov_A2_obligation_int : classical_A2_obligation_int := by
  intro s t hs ht hc
  have hsum : s.radius + t.radius ≠ 0 := by positivity
  set μ := s.radius / (s.radius + t.radius) with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one (by positivity)]; linarith
  refine ⟨AffineMap.lineMap s.center t.center μ, ⟨⟨μ, ⟨hμ0, hμ1⟩, rfl⟩, ?_⟩, fun I hI => ?_⟩
  · rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hμ0, abs_of_nonneg (by linarith), hμ]
    field_simp
    ring
  · have h1 := int_eq_of_isInt s t hs ht hc I hI
    have h2 := int_eq_of_isInt s t hs ht hc _ ⟨⟨μ, ⟨hμ0, hμ1⟩, rfl⟩, by
      rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hμ0, abs_of_nonneg (by linarith), hμ]
      field_simp
      ring⟩
    exact smul_right_injective _ hsum (h1.trans h2.symm)

end Monge.Classical
