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

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace Brockian.Equidistribution

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- The empirical measure of the first `N + 1` terms of the sequence `x`: the average of the
Dirac masses at `x 0, …, x N`. -/
noncomputable def empiricalMeasure (x : ℕ → X) (N : ℕ) : Measure X :=
  ((N : ℝ≥0∞) + 1)⁻¹ • ∑ n ∈ Finset.range (N + 1), Measure.dirac (x n)

instance instIsProbabilityMeasureEmpiricalMeasure (x : ℕ → X) (N : ℕ) :
    IsProbabilityMeasure (empiricalMeasure x N) := by
  constructor
  simp only [empiricalMeasure, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
    smul_eq_mul]
  simp [ENNReal.inv_mul_cancel]

/-- Integrating a continuous function against the empirical measure gives the Cesàro average. -/
lemma integral_empiricalMeasure (x : ℕ → X) (N : ℕ) (f : C(X, ℝ)) :
    ∫ y, f y ∂(empiricalMeasure x N) =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), f (x n) := by
  rw [empiricalMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun i _ => integrable_dirac (by simp [enorm_eq_nnnorm]))]
  simp [ENNReal.toReal_inv, ENNReal.toReal_add]

/-- The empirical measures, viewed as elements of the space of probability measures. -/
noncomputable def empiricalProbabilityMeasure (x : ℕ → X) (N : ℕ) : ProbabilityMeasure X :=
  ⟨empiricalMeasure x N, inferInstance⟩

/-- **Existence of asymptotic averages implies equidistribution with respect to some probability
measure.**

Let `X` be a compact Hausdorff space with its Borel σ-algebra and let `x : ℕ → X` be a sequence.
If for every continuous real-valued function `f` on `X` the Cesàro averages
`(1/N) * ∑_{n < N} f (x n)` converge to *some* real number, then there is a single Borel
probability measure `μ` on `X` such that these averages converge to `∫ f dμ` for every continuous
`f`; that is, `x` is equidistributed with respect to `μ`.

The measure is produced unconditionally: nothing about the existence of a limiting measure is
assumed, only the existence of the scalar limits. -/
theorem equidistribution_of_asymptotic_exists (x : ℕ → X)
    (h : ∀ f : C(X, ℝ), ∃ L : ℝ,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)) atTop (𝓝 L)) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X, ℝ),
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)) atTop
        (𝓝 (∫ y, f y ∂(μ : Measure X))) := by
  -- The space of probability measures on a compact space is compact, so the sequence of
  -- empirical measures has a cluster point `μ`.
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace (map (empiricalProbabilityMeasure x) atTop)
  refine ⟨μ, fun f => ?_⟩
  obtain ⟨L, hL⟩ := h f
  -- The averages along the shifted index also tend to `L`.
  have hL' : Tendsto
      (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), f (x n)) atTop (𝓝 L) := by
    have := hL.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  -- Integration against `f` is continuous on the space of probability measures.
  have hcont : Continuous fun ν : ProbabilityMeasure X => ∫ y, f y ∂(ν : Measure X) :=
    ProbabilityMeasure.continuous_integral_continuousMap f
  have htend : Tendsto (fun ν : ProbabilityMeasure X => ∫ y, f y ∂(ν : Measure X))
      (map (empiricalProbabilityMeasure x) atTop) (𝓝 L) := by
    rw [tendsto_map'_iff]
    refine hL'.congr fun N => ?_
    exact (integral_empiricalMeasure x N f).symm
  -- Hence `∫ f dμ` is a cluster point of a filter converging to `L`, so it equals `L`.
  have hEq : ∫ y, f y ∂(μ : Measure X) = L := eq_of_nhds_neBot (hμ.map hcont.continuousAt htend)
  rw [hEq]
  exact hL

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
/-- The hypothesis of `equidistribution_of_asymptotic_exists` is satisfiable: a constant sequence
has asymptotic averages for every continuous function. -/
lemma asymptotic_exists_of_const (c : X) :
    ∀ f : C(X, ℝ), ∃ L : ℝ,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f ((fun _ : ℕ => c) n)) atTop
        (𝓝 L) := by
  refine fun f => ⟨f c, ?_⟩
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  field_simp
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

end Brockian.Equidistribution

