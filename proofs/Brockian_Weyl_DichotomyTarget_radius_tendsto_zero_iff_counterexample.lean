/-
  Aristotle target — the Weyl b→∞ limit-point/limit-circle DICHOTOMY (radius side).

  This is the missing link between the verified finite-b nested-circle geometry
  (`Brockian.Weyl.Disk`: radius r_b = 1/(2|Im λ|·∫₀ᵇ|φ|²), monotone) and the
  essential-self-adjointness criterion (`Brockian.Weyl.Cayley`).

  The mathematical core is a self-contained real-analysis fact: for a positive
  constant c and a nonnegative nondecreasing accumulation I(b) (= ∫₀ᵇ|φ|²),
      r(b) = 1/(2·c·I(b))  →  0   as b → ∞   ⟺   I(b) → ∞.
  (limit-point side: radius shrinks to a point iff the L² mass diverges.)

  The originally requested equivalence omitted the necessary condition that the
  mass is positive somewhere. In Lean's field convention, `1 / 0 = 0`, so the
  identically-zero mass is a counterexample: its radius is identically zero but
  its mass does not tend to `+∞`. The counterexample is proved below, followed by
  the corrected nondegenerate equivalence and the two valid requested results.
-/
import Mathlib

open Filter Topology

namespace Brockian.Weyl.DichotomyTarget

/-- The hypotheses in the originally proposed `radius_tendsto_zero_iff` do not
suffice: the identically-zero mass is a counterexample because Lean defines
`1 / 0 = 0`. -/
theorem radius_tendsto_zero_iff_counterexample :
    ∃ (c : ℝ) (I : ℝ → ℝ),
      0 < c ∧ (∀ b, 0 ≤ I b) ∧ Monotone I ∧
      Tendsto (fun b => 1 / (2 * c * I b)) atTop (𝓝 0) ∧
      ¬ Tendsto I atTop atTop := by
  use 1, fun _ => 0
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · exact fun _ => le_refl 0
  · exact monotone_const
  · simp
  · intro h
    exact not_tendsto_atTop_of_tendsto_nhds (tendsto_const_nhds (x := (0 : ℝ))) h

/-
The requested theorem cannot be retained as a declaration, since the preceding
counterexample proves it false. Its exact original statement was:

theorem radius_tendsto_zero_iff (c : ℝ) (hc : 0 < c)
    (I : ℝ → ℝ) (hI0 : ∀ b, 0 ≤ I b) (hImono : Monotone I) :
    Tendsto (fun b => 1 / (2 * c * I b)) atTop (𝓝 0) ↔ Tendsto I atTop atTop
-/

/-- **The radius dichotomy (nondegenerate core).** Positivity of the accumulated
mass somewhere excludes the identically-zero counterexample and is the condition
satisfied in the Weyl application. -/
theorem radius_tendsto_zero_iff_of_pos (c : ℝ) (hc : 0 < c)
    (I : ℝ → ℝ) (hI0 : ∀ b, 0 ≤ I b) (hImono : Monotone I)
    (hIpos : ∃ b, 0 < I b) :
    Tendsto (fun b => 1 / (2 * c * I b)) atTop (𝓝 0) ↔ Tendsto I atTop atTop := by
  constructor
  · intro hr
    obtain ⟨b₀, hb₀⟩ := hIpos
    have hc2 : 0 < 2 * c := by positivity
    have hevent : ∀ᶠ b in atTop, 2 * c * I b > 0 := by
      filter_upwards [eventually_ge_atTop b₀] with b hb
      exact mul_pos hc2 (lt_of_lt_of_le hb₀ (hImono hb))
    have hinv : Tendsto (fun b => (2 * c * I b)⁻¹) atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · simpa only [one_div] using hr
      · filter_upwards [hevent] with b hb
        exact inv_pos.mpr hb
    have hx := hinv.inv_tendsto_nhdsGT_zero
    have hprod : Tendsto (fun b => 2 * c * I b) atTop atTop := by
      convert hx using 1
      ext b
      simp
    exact (tendsto_const_mul_atTop_of_pos hc2).mp hprod
  · intro hdiv
    have hc2 : 0 < 2 * c := by positivity
    have hprod : Tendsto (fun b => 2 * c * I b) atTop atTop :=
      Tendsto.const_mul_atTop hc2 hdiv
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hprod

/-- The limit-point case: if the L² mass diverges, the radius collapses to a point. -/
theorem radius_to_zero_of_mass_infinite (c : ℝ) (hc : 0 < c)
    (I : ℝ → ℝ) (hI0 : ∀ b, 0 ≤ I b) (hImono : Monotone I)
    (hdiv : Tendsto I atTop atTop) :
    Tendsto (fun b => 1 / (2 * c * I b)) atTop (𝓝 0) := by
  have hc2 : 0 < 2 * c := by linarith
  have hprod : Tendsto (fun b => 2 * c * I b) atTop atTop :=
    Tendsto.const_mul_atTop hc2 hdiv
  simp_rw [one_div]
  exact tendsto_inv_atTop_zero.comp hprod

/-- The limit-circle case: if the L² mass stays finite, the radius has a positive limit. -/
theorem radius_pos_limit_of_mass_finite (c : ℝ) (hc : 0 < c)
    (I : ℝ → ℝ) (hI0 : ∀ b, 0 ≤ I b) (hImono : Monotone I)
    (L : ℝ) (hL : 0 < L) (hconv : Tendsto I atTop (𝓝 L)) :
    Tendsto (fun b => 1 / (2 * c * I b)) atTop (𝓝 (1 / (2 * c * L))) := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hc_ne : 2 * c ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hc)
  have hcont : ContinuousAt (fun x => 1 / (2 * c * x)) L := by
    apply ContinuousAt.div continuousAt_const
    · exact continuousAt_const.mul continuousAt_id
    · exact mul_ne_zero hc_ne hL_ne
  exact hcont.tendsto.comp hconv

end Brockian.Weyl.DichotomyTarget

