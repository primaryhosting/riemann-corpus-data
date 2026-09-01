import Mathlib
namespace Brockian.MsMenelaus

/-- If `A`, `B`, `C` are not collinear, then `B - A` and `C - A` are linearly independent,
stated concretely as: any vanishing linear combination has zero coefficients. -/
lemma indep_of_not_collinear {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A B C : V) (h : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    ∀ x y : ℝ, x • (B - A) + y • (C - A) = 0 → x = 0 ∧ y = 0 := by
  intro x y hxy
  constructor
  · by_contra hx
    apply h
    rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
    refine ⟨C - A, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    refine ⟨⟨0, by simp⟩, ⟨x⁻¹ * (-y), ?_⟩, ⟨1, by simp⟩⟩
    have h2 : x • (B - A) = (-y) • (C - A) := by linear_combination (norm := module) hxy
    have h3 := congrArg (fun z => (x⁻¹ : ℝ) • z) h2
    simp only [smul_smul, inv_mul_cancel₀ hx, one_smul] at h3
    rw [vadd_eq_add, ← h3]; abel
  · by_contra hy
    apply h
    rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
    refine ⟨B - A, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    refine ⟨⟨0, by simp⟩, ⟨1, by simp⟩, ⟨y⁻¹ * (-x), ?_⟩⟩
    have h2 : y • (C - A) = (-x) • (B - A) := by linear_combination (norm := module) hxy
    have h3 := congrArg (fun z => (y⁻¹ : ℝ) • z) h2
    simp only [smul_smul, inv_mul_cancel₀ hy, one_smul] at h3
    rw [vadd_eq_add, ← h3]; abel

/-- Collinearity criterion for three points written in coordinates with respect to a
linearly independent pair of vectors `b`, `c`: the corresponding determinant vanishes. -/
lemma collinear_triple_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b c : V) (hbc : ∀ x y : ℝ, x • b + y • c = 0 → x = 0 ∧ y = 0)
    (P : V) (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) :
    Collinear ℝ ({P + x₁ • b + y₁ • c, P + x₂ • b + y₂ • c, P + x₃ • b + y₃ • c} : Set V)
      ↔ (x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁) = 0 := by
  constructor
  · intro hcol
    rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r₂, h2⟩ := hv _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨r₃, h3⟩ := hv _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    rw [vadd_eq_add] at h2 h3
    have e2 : (x₂ - x₁) • b + (y₂ - y₁) • c = r₂ • v := by
      linear_combination (norm := module) h2
    have e3 : (x₃ - x₁) • b + (y₃ - y₁) • c = r₃ • v := by
      linear_combination (norm := module) h3
    have key : (r₃ * (x₂ - x₁) - r₂ * (x₃ - x₁)) • b
        + (r₃ * (y₂ - y₁) - r₂ * (y₃ - y₁)) • c = 0 := by
      linear_combination (norm := module) r₃ • e2 - r₂ • e3
    obtain ⟨kx, ky⟩ := hbc _ _ key
    by_cases hr₂ : r₂ = 0
    · subst hr₂
      have e2' : (x₂ - x₁) • b + (y₂ - y₁) • c = 0 := by rw [e2]; simp
      obtain ⟨p, q⟩ := hbc _ _ e2'
      rw [show x₂ - x₁ = 0 from p, show y₂ - y₁ = 0 from q]; ring
    · have hz : r₂ * ((x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)) = 0 := by
        linear_combination (y₂ - y₁) * kx - (x₂ - x₁) * ky
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h hr₂
      · exact h
  · intro hdet
    rw [collinear_iff_of_mem (Set.mem_insert _ _)]
    by_cases hx : x₂ - x₁ = 0 ∧ y₂ - y₁ = 0
    · obtain ⟨hx2, hy2⟩ := hx
      refine ⟨(x₃ - x₁) • b + (y₃ - y₁) • c, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
      refine ⟨⟨0, by rw [vadd_eq_add]; module⟩,
        ⟨0, by rw [vadd_eq_add, show x₂ = x₁ by linarith, show y₂ = y₁ by linarith]; module⟩,
        ⟨1, by rw [vadd_eq_add]; module⟩⟩
    · have ht : ∃ t : ℝ, x₃ = x₁ + t * (x₂ - x₁) ∧ y₃ = y₁ + t * (y₂ - y₁) := by
        by_cases hx2 : x₂ - x₁ = 0
        · have hy2 : y₂ - y₁ ≠ 0 := fun h => hx ⟨hx2, h⟩
          refine ⟨(y₃ - y₁) / (y₂ - y₁), ?_, ?_⟩
          · have hxx : (x₃ - x₁) * (y₂ - y₁) = 0 := by
              linear_combination -hdet + (y₃ - y₁) * hx2
            rcases mul_eq_zero.1 hxx with h | h
            · rw [hx2]; linarith
            · exact absurd h hy2
          · field_simp
            ring
        · refine ⟨(x₃ - x₁) / (x₂ - x₁), ?_, ?_⟩
          · field_simp
            ring
          · field_simp
            linear_combination hdet
      obtain ⟨t, hx3, hy3⟩ := ht
      subst hx3 hy3
      refine ⟨(x₂ - x₁) • b + (y₂ - y₁) • c, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
      refine ⟨⟨0, by rw [vadd_eq_add]; module⟩, ⟨1, by rw [vadd_eq_add]; module⟩,
        ⟨t, by rw [vadd_eq_add]; module⟩⟩

/-- Menelaus's theorem: points D, E, F on lines BC, CA, AB (with parameters u, v, w) are
    collinear iff the product of signed ratios (u/(1−u))·(v/(1−v))·(w/(1−w)) = −1.

    (Statement adjusted: the nondegeneracy hypothesis `hABC`, that `A`, `B`, `C` form a genuine
    triangle, is required; without it, for a degenerate "triangle" all points are always
    collinear while the product of ratios is arbitrary.) -/
theorem menelaus (A B C : EuclideanSpace ℝ (Fin 2)) (u v w : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hu : u ≠ 1) (hv : v ≠ 1) (hw : w ≠ 1)
    (D E F : EuclideanSpace ℝ (Fin 2))
    (hD : D = B + u • (C - B)) (hE : E = C + v • (A - C)) (hF : F = A + w • (B - A)) :
    Collinear ℝ ({D, E, F} : Set (EuclideanSpace ℝ (Fin 2)))
      ↔ (u / (1 - u)) * (v / (1 - v)) * (w / (1 - w)) = -1 := by
  have hbc := indep_of_not_collinear A B C hABC
  have hu' : (1 : ℝ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hv' : (1 : ℝ) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have hw' : (1 : ℝ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hDc : D = A + (1 - u) • (B - A) + u • (C - A) := by
    rw [hD]; module
  have hEc : E = A + (0 : ℝ) • (B - A) + (1 - v) • (C - A) := by
    rw [hE]; module
  have hFc : F = A + w • (B - A) + (0 : ℝ) • (C - A) := by
    rw [hF]; module
  have hprod : (1 - u) * (1 - v) * (1 - w) ≠ 0 := mul_ne_zero (mul_ne_zero hu' hv') hw'
  rw [hDc, hEc, hFc, collinear_triple_iff (B - A) (C - A) hbc,
    div_mul_div_comm, div_mul_div_comm, div_eq_iff hprod]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

end Brockian.MsMenelaus

