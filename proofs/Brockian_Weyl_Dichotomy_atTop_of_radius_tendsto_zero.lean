/-
  Brockian/WeylDichotomy.lean — the `b → ∞` radius side of the Weyl
  limit-point / limit-circle dichotomy, as pure real analysis.

  From `Brockian.Weyl.Disk` the classical Weyl radius is
      r_b = 1 / (2 |Im λ| · ∫₀ᵇ |φ|²)
  with antitone nesting. The dichotomy at ∞, on the radii alone, is:
      r_b → 0   ⇔   mass I → +∞     (limit-point radius)
      mass bounded above              (limit-circle radius)

  Self-contained fact about a positive scale `c` (for `|Im λ|`) and an
  accumulator `I : ℝ → ℝ`. Does **not** claim operator-theoretic
  limit-point, `ran(T±i)` density, or ess-self-adjointness of `−Δ+V`.

  Verification: AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

open Filter Topology Set

namespace Brockian.Weyl.Dichotomy

/-- The Weyl radius shape `r = 1 / (2 c · I)`. -/
noncomputable def weylRadius (c : ℝ) (I : ℝ → ℝ) (b : ℝ) : ℝ :=
  1 / (2 * c * I b)

/-- **Mass diverges ⇒ radius collapses.** -/
theorem radius_tendsto_zero_of_atTop {c : ℝ} (hc : 0 < c) {I : ℝ → ℝ}
    (hI : Tendsto I atTop atTop) :
    Tendsto (weylRadius c I) atTop (nhds 0) := by
  have h2c : (0 : ℝ) < 2 * c := mul_pos two_pos hc
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- I ≥ 1/(2cε) + 1 > 1/(2cε) ⇒ 1/(2c I) < ε
  let T : ℝ := 1 / (2 * c * ε) + 1
  have hTpos : (0 : ℝ) < T := by positivity
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hI T
  refine eventually_atTop.mpr ⟨N, fun b hb => ?_⟩
  have hIb : T ≤ I b := hN b hb
  have hIpos : (0 : ℝ) < I b := lt_of_lt_of_le hTpos hIb
  have hgt : 1 / (2 * c * ε) < I b :=
    lt_of_lt_of_le (by linarith : 1 / (2 * c * ε) < T) hIb
  have hden : (0 : ℝ) < 2 * c * I b := mul_pos h2c hIpos
  simp only [Real.dist_eq, weylRadius, sub_zero]
  have hrnn : 0 ≤ 1 / (2 * c * I b) := one_div_nonneg.mpr (le_of_lt hden)
  rw [abs_of_nonneg hrnn]
  have hmul' : 2 * c * (1 / (2 * c * ε)) < 2 * c * I b :=
    mul_lt_mul_of_pos_left hgt h2c
  have hsimp : 2 * c * (1 / (2 * c * ε)) = 1 / ε := by field_simp
  have hmul : 1 / ε < 2 * c * I b := by rwa [hsimp] at hmul'
  have h1 : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
  have hlt : 1 / (2 * c * I b) < 1 / (1 / ε) :=
    (one_div_lt_one_div hden h1).mpr hmul
  rwa [one_div_one_div] at hlt

/-- **Radius collapses ⇒ mass diverges** (under eventual positivity of `I`). -/
theorem atTop_of_radius_tendsto_zero {c : ℝ} (hc : 0 < c) {I : ℝ → ℝ}
    (hpos : ∀ᶠ b in atTop, 0 < I b)
    (hr : Tendsto (weylRadius c I) atTop (nhds 0)) :
    Tendsto I atTop atTop := by
  have h2c : (0 : ℝ) < 2 * c := mul_pos two_pos hc
  refine tendsto_atTop_atTop.mpr fun M => ?_
  let M' : ℝ := max M 0 + 1
  have hM'pos : (0 : ℝ) < M' := by
    have : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    linarith
  have hε : (0 : ℝ) < 1 / (2 * c * M') := by positivity
  have hnear : ∀ᶠ b in atTop, dist (weylRadius c I b) 0 < 1 / (2 * c * M') :=
    (Metric.tendsto_nhds.mp hr) _ hε
  have hcomb : ∀ᶠ b in atTop,
      dist (weylRadius c I b) 0 < 1 / (2 * c * M') ∧ 0 < I b :=
    hnear.and hpos
  obtain ⟨B, hB⟩ := eventually_atTop.mp hcomb
  refine ⟨B, fun b hb => ?_⟩
  obtain ⟨hdist, hrpos⟩ := hB b hb
  simp only [Real.dist_eq, weylRadius, sub_zero] at hdist
  have hden : (0 : ℝ) < 2 * c * I b := mul_pos h2c hrpos
  have hrnn : 0 ≤ 1 / (2 * c * I b) := one_div_nonneg.mpr (le_of_lt hden)
  rw [abs_of_nonneg hrnn] at hdist
  have hdenM : (0 : ℝ) < 2 * c * M' := mul_pos h2c hM'pos
  have hinv : 2 * c * M' < 2 * c * I b :=
    (one_div_lt_one_div hden hdenM).mp hdist
  have hIgt : M' < I b := lt_of_mul_lt_mul_left hinv (le_of_lt h2c)
  have hMle : M ≤ max M 0 := le_max_left _ _
  linarith

/-- **Core equivalence** under eventual positivity of `I`. -/
theorem radius_tendsto_zero_iff {c : ℝ} (hc : 0 < c) {I : ℝ → ℝ}
    (hpos : ∀ᶠ b in atTop, 0 < I b) :
    Tendsto (weylRadius c I) atTop (nhds 0) ↔ Tendsto I atTop atTop :=
  ⟨atTop_of_radius_tendsto_zero hc hpos, radius_tendsto_zero_of_atTop hc⟩

/-- **Monotone and unbounded above ⇒ tendsto `atTop`.** -/
theorem tendsto_atTop_of_monotone_not_bddAbove {I : ℝ → ℝ}
    (hmono : Monotone I) (hunb : ¬ BddAbove (range I)) :
    Tendsto I atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun M => ?_
  have : ∃ x₀, M < I x₀ := by
    by_contra h
    push_neg at h
    exact hunb ⟨M, by
      rintro y ⟨x, rfl⟩
      exact h x⟩
  obtain ⟨x₀, hx₀⟩ := this
  exact ⟨x₀, fun x hx => le_trans (le_of_lt hx₀) (hmono hx)⟩

/-- **Limit-point radius:** `range I` is not bounded above. -/
def IsLimitPointRadius (I : ℝ → ℝ) : Prop :=
  ¬ BddAbove (range I)

/-- **Limit-circle radius:** `range I` is bounded above. -/
def IsLimitCircleRadius (I : ℝ → ℝ) : Prop :=
  BddAbove (range I)

/-- **Radius dichotomy.** -/
theorem limitPoint_or_limitCircle_radius (I : ℝ → ℝ) :
    IsLimitPointRadius I ∨ IsLimitCircleRadius I := by
  cases Classical.em (BddAbove (range I)) with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

/-- **Limit-point radius ⇒ radius → 0** (under monotonicity). -/
theorem limitPointRadius_radius_tendsto_zero {c : ℝ} (hc : 0 < c) {I : ℝ → ℝ}
    (hmono : Monotone I) (h : IsLimitPointRadius I) :
    Tendsto (weylRadius c I) atTop (nhds 0) :=
  radius_tendsto_zero_of_atTop hc (tendsto_atTop_of_monotone_not_bddAbove hmono h)

end Brockian.Weyl.Dichotomy
