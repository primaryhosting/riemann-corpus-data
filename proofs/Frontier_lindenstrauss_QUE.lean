import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

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

namespace Frontier

open MeasureTheory Filter Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Weak-\* compactness reduction.**  If every subsequential weak-\* limit of a sequence of
probability measures on a compact metric space equals `vol`, then the whole sequence converges
weak-\* to `vol`. -/
theorem tendsto_of_forall_subseq_limit_eq
    (μ : ℕ → ProbabilityMeasure X) (vol : ProbabilityMeasure X)
    (h : ∀ ns : ℕ → ℕ, StrictMono ns → ∀ ν : ProbabilityMeasure X,
      Tendsto (fun k => μ (ns k)) atTop (𝓝 ν) → ν = vol) :
    Tendsto μ atTop (𝓝 vol) := by
  by_contra hcon
  rw [Filter.tendsto_iff_forall_eventually_mem] at hcon
  push_neg at hcon
  obtain ⟨U, hU, hfreq⟩ := hcon
  obtain ⟨ψ, hψ, hψU⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ν, ms, hms, htend⟩ := CompactSpace.tendsto_subseq (fun k => μ (ψ k))
  have hν : ν = vol := h (ψ ∘ ms) (hψ.comp hms) ν htend
  subst hν
  have hev : ∀ᶠ k in atTop, μ (ψ (ms k)) ∈ U := htend hU
  obtain ⟨k, hk⟩ := hev.exists
  exact hψU (ms k) hk

/-- The measure `|f|² · vol`, the natural "quantum probability measure" attached to an
`L²`-normalised (eigen)function `f`. -/
noncomputable def sqDensityMeasure (vol : Measure X) (f : C(X, ℝ)) : Measure X :=
  vol.withDensity (fun x => (Real.toNNReal (f x ^ 2) : ℝ≥0∞))

omit [CompactSpace X] in
lemma integral_sqDensityMeasure (vol : Measure X) (f g : C(X, ℝ)) :
    ∫ x, g x ∂(sqDensityMeasure vol f) = ∫ x, g x * f x ^ 2 ∂vol := by
  rw [sqDensityMeasure, integral_withDensity_eq_integral_smul]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (Real.toNNReal (f x ^ 2)) • g x = g x * f x ^ 2
    rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg (f x)), smul_eq_mul, mul_comm]
  · exact measurable_real_toNNReal.comp (f.continuous.pow 2).measurable

lemma isProbabilityMeasure_sqDensityMeasure (vol : Measure X) [IsProbabilityMeasure vol]
    (f : C(X, ℝ)) (hf : ∫ x, f x ^ 2 ∂vol = 1) :
    IsProbabilityMeasure (sqDensityMeasure vol f) := by
  constructor
  have hint : Integrable (fun x => f x ^ 2) vol :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [sqDensityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hlint : ∫⁻ x, (Real.toNNReal (f x ^ 2) : ℝ≥0∞) ∂vol = ENNReal.ofReal (∫ x, f x ^ 2 ∂vol) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    rfl
  rw [hlint, hf, ENNReal.ofReal_one]

/-- **Arithmetic Quantum Unique Ergodicity (Lindenstrauss), in reduced form.**

Setting: a compact metric space `X` (the congruence surface, or its unit cotangent bundle)
carrying a normalised volume measure `vol`, and a sequence `phi` of `L²`-normalised real
functions (the Hecke–Maass eigenfunctions).

Hypothesis `hQL` is exactly the classification of quantum limits which is the content of
Lindenstrauss' theorem: every weak-\* limit `ν` of the sequence of microlocal lifts
`|phi n|² vol` along a subsequence is the normalised volume measure.

Conclusion: the full sequence of probability densities `|phi n|²` equidistributes, i.e.
`∫ g |phi n|² dvol → ∫ g dvol` for every continuous observable `g`.

The proof is the weak-\* compactness argument reducing QUE to the classification of quantum
limits. -/
theorem lindenstrauss_QUE
    (vol : Measure X) [IsProbabilityMeasure vol]
    (phi : ℕ → C(X, ℝ)) (hnorm : ∀ n, ∫ x, (phi n x) ^ 2 ∂vol = 1)
    (hQL : ∀ ns : ℕ → ℕ, StrictMono ns → ∀ ν : Measure X, IsProbabilityMeasure ν →
      (∀ g : C(X, ℝ),
        Tendsto (fun k => ∫ x, g x * (phi (ns k) x) ^ 2 ∂vol) atTop (𝓝 (∫ x, g x ∂ν))) →
      ν = vol) :
    ∀ g : C(X, ℝ),
      Tendsto (fun n => ∫ x, g x * (phi n x) ^ 2 ∂vol) atTop (𝓝 (∫ x, g x ∂vol)) := by
  have hprob : ∀ n, IsProbabilityMeasure (sqDensityMeasure vol (phi n)) := fun n =>
    isProbabilityMeasure_sqDensityMeasure vol (phi n) (hnorm n)
  set μ : ℕ → ProbabilityMeasure X := fun n => ⟨sqDensityMeasure vol (phi n), hprob n⟩ with hμ
  set volP : ProbabilityMeasure X := ⟨vol, ‹IsProbabilityMeasure vol›⟩ with hvolP
  have key : Tendsto μ atTop (𝓝 volP) := by
    refine tendsto_of_forall_subseq_limit_eq μ volP (fun ns hns ν hconv => Subtype.ext ?_)
    refine hQL ns hns (ν : Measure X) ν.2 (fun g => ?_)
    have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv
      (BoundedContinuousFunction.mkOfCompact g)
    simpa [hμ, integral_sqDensityMeasure] using this
  intro g
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp key
    (BoundedContinuousFunction.mkOfCompact g)
  simpa [hμ, hvolP, integral_sqDensityMeasure] using this

end Frontier

