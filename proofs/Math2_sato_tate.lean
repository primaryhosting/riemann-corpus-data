/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real ENNReal NNReal Classical
open MeasureTheory Filter Topology Set

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/
noncomputable def satoTateDensity (x : ℝ) : ℝ := 2 / Real.pi * Real.sin x ^ 2

/-- The Sato–Tate measure: the measure on `ℝ` with density `(2/π) sin²θ` supported on `[0, π]`. -/
noncomputable def satoTateMeasure : Measure ℝ :=
  (volume.restrict (Set.Icc 0 Real.pi)).withDensity fun x => ENNReal.ofReal (satoTateDensity x)

lemma satoTateDensity_nonneg (x : ℝ) : 0 ≤ satoTateDensity x := by
  have h : (0:ℝ) < Real.pi := Real.pi_pos
  unfold satoTateDensity
  positivity

/-- The value of the Sato–Tate integral over an interval. -/
lemma lintegral_satoTateDensity_Icc {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ x in Set.Icc a b, ENNReal.ofReal (satoTateDensity x) =
      ENNReal.ofReal ((b - a - (Real.sin b * Real.cos b - Real.sin a * Real.cos a)) / Real.pi) := by
  have hcont : Continuous satoTateDensity := by unfold satoTateDensity; fun_prop
  have hint : IntegrableOn satoTateDensity (Set.Icc a b) := hcont.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall satoTateDensity_nonneg)]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  unfold satoTateDensity
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The Sato–Tate mass of an interval is nonnegative. -/
lemma satoTate_value_nonneg {a b : ℝ} (hab : a ≤ b) :
    0 ≤ (b - a - (Real.sin b * Real.cos b - Real.sin a * Real.cos a)) / Real.pi := by
  have h : (0:ℝ) ≤ ∫ x in a..b, Real.sin x ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  rw [integral_sin_sq] at h
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  apply div_nonneg _ hpi.le
  linarith

/-- The Sato–Tate measure of a subinterval `[a,b] ⊆ [0,π]`. -/
theorem satoTateMeasure_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    satoTateMeasure (Set.Icc a b) =
      ENNReal.ofReal ((b - a - (Real.sin b * Real.cos b - Real.sin a * Real.cos a)) / Real.pi) := by
  rw [satoTateMeasure, withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_self_of_subset_left (Set.Icc_subset_Icc ha hb),
    lintegral_satoTateDensity_Icc hab]

/-- The Sato–Tate measure is a probability measure. -/
instance satoTate_isProbabilityMeasure : IsProbabilityMeasure satoTateMeasure := by
  constructor
  rw [satoTateMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_satoTateDensity_Icc Real.pi_pos.le]
  simp [Real.pi_ne_zero]

/-- The Sato–Tate distribution, as a probability measure on `ℝ`. -/
noncomputable def satoTateProb : ProbabilityMeasure ℝ := ⟨satoTateMeasure, inferInstance⟩

/-- The Sato–Tate measure has no atoms. -/
lemma satoTateMeasure_singleton (x : ℝ) : satoTateMeasure {x} = 0 := by
  rw [satoTateMeasure, withDensity_apply _ (measurableSet_singleton x)]
  refine setLIntegral_measure_zero _ _ ?_
  simp

/-- The Sato–Tate measure gives no mass to the boundary of an interval. -/
lemma satoTateMeasure_frontier_Icc (a b : ℝ) : satoTateMeasure (frontier (Set.Icc a b)) = 0 := by
  have hsub : frontier (Set.Icc a b) ⊆ {a, b} := by
    intro x hx
    have h1 : x ∈ closure (Set.Icc a b) := frontier_subset_closure hx
    have h2 : x ∉ interior (Set.Icc a b) := by
      rw [frontier] at hx; exact hx.2
    rw [closure_Icc] at h1
    rw [interior_Icc] at h2
    simp only [Set.mem_Ioo, not_and_or, not_lt] at h2
    rcases h2 with h | h
    · exact Or.inl (le_antisymm h h1.1)
    · exact Or.inr (le_antisymm h1.2 h)
  refine measure_mono_null hsub ?_
  rw [Set.insert_eq]
  exact measure_union_null (satoTateMeasure_singleton a) (satoTateMeasure_singleton b)

/-- The Frobenius angle attached to a trace of Frobenius `a` at a prime `p`:
`θ_p = arccos (a_p / (2√p))`, where `a_p = p + 1 - #E(𝔽_p)`. -/
noncomputable def frobeniusAngle (a : ℤ) (p : ℕ) : ℝ :=
  Real.arccos ((a : ℝ) / (2 * Real.sqrt p))

lemma frobeniusAngle_mem_Icc (a : ℤ) (p : ℕ) : frobeniusAngle a p ∈ Set.Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- Under the Hasse bound `|a_p| ≤ 2√p`, the Frobenius angle satisfies
`a_p = 2 √p cos θ_p`. -/
lemma cos_frobeniusAngle {a : ℤ} {p : ℕ} (hp : 0 < p)
    (hasse : |(a : ℝ)| ≤ 2 * Real.sqrt p) :
    2 * Real.sqrt p * Real.cos (frobeniusAngle a p) = (a : ℝ) := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp)
  have h2 : (0:ℝ) < 2 * Real.sqrt p := by linarith
  have habs : |(a:ℝ) / (2 * Real.sqrt p)| ≤ 1 := by
    rw [abs_div, abs_of_pos h2, div_le_one h2]; exact hasse
  rw [abs_le] at habs
  rw [frobeniusAngle, Real.cos_arccos habs.1 habs.2]
  field_simp

/-- The empirical distribution of the first `N` terms of a sequence of angles. -/
noncomputable def empiricalMeasure (θ : ℕ → ℝ) (N : ℕ) : Measure ℝ :=
  (N : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range N, Measure.dirac (θ i)

lemma empiricalMeasure_apply (θ : ℕ → ℝ) (N : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    empiricalMeasure θ N s =
      (N : ℝ≥0∞)⁻¹ * ((Finset.range N).filter fun i => θ i ∈ s).card := by
  simp [empiricalMeasure, Measure.smul_apply, Measure.dirac_apply' _ hs, Set.indicator_apply,
    Finset.sum_boole]

/-- **The Sato–Tate distribution of Frobenius angles.**

Let `θ : ℕ → ℝ` enumerate the Frobenius angles `θ_p = arccos (a_p / (2√p))` of an elliptic
curve without complex multiplication, and let `μs N` be the empirical distribution of the first
`N` of them.  The Sato–Tate conjecture — a theorem of Clozel–Harris–Shepherd-Barron–Taylor for
non-CM curves over `ℚ` (and over totally real fields), whose proof is far beyond what is
currently formalized — states that `μs` converges weakly to the Sato–Tate measure
`(2/π) sin²θ dθ` on `[0, π]`.  This is taken here as the hypothesis `hST`.

The conclusion is the resulting distribution statement: for every subinterval `[a,b] ⊆ [0,π]`,
the proportion of the first `N` Frobenius angles lying in `[a,b]` converges to
`(2/π) ∫_a^b sin²θ dθ = (b - a - (sin b cos b - sin a cos a))/π`. -/
theorem sato_tate (θ : ℕ → ℝ) (μs : ℕ → ProbabilityMeasure ℝ)
    (hemp : ∀ N, 0 < N → (μs N : Measure ℝ) = empiricalMeasure θ N)
    (hST : Tendsto μs atTop (𝓝 satoTateProb))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    Tendsto
      (fun N : ℕ => (((Finset.range N).filter fun i => θ i ∈ Set.Icc a b).card : ℝ) / N)
      atTop
      (𝓝 ((b - a - (Real.sin b * Real.cos b - Real.sin a * Real.cos a)) / Real.pi)) := by
  have hnull : (satoTateProb : Measure ℝ) (frontier (Set.Icc a b)) = 0 :=
    satoTateMeasure_frontier_Icc a b
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hST hnull
  have hlim : ((satoTateProb : Measure ℝ) (Set.Icc a b)).toReal =
      (b - a - (Real.sin b * Real.cos b - Real.sin a * Real.cos a)) / Real.pi := by
    show (satoTateMeasure (Set.Icc a b)).toReal = _
    rw [satoTateMeasure_Icc ha hab hb,
      ENNReal.toReal_ofReal (satoTate_value_nonneg hab)]
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (satoTateProb : Measure ℝ) _)).comp key
  rw [Function.comp_def, hlim] at hreal
  refine hreal.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  rw [hemp N hN, empiricalMeasure_apply θ N measurableSet_Icc]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    div_eq_inv_mul]
  simp

end Math2

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

