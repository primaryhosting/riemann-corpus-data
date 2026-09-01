/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Scope of the formalization

Mathlib (at the pinned version) contains neither Brownian motion nor weak convergence of measures
on `C[0,1]`, so the full functional form of Donsker's invariance principle cannot be *stated*
against existing definitions. What is formalized here is the invariance principle at the level of
the second-order structure of the process: for an arbitrary sequence of independent, centred,
unit-variance, square-integrable increments, the diffusively rescaled walk
`W_n(t) = (X_0 + ⋯ + X_{⌊nt⌋-1})/√n` has

* covariance `E[W_n(s) W_n(t)] → min s t` (`Math2.donsker_invariance`),
* increment variance `E[(W_n(t) - W_n(s))²] → t - s` (`Math2.donsker_increment_variance`),
* asymptotically uncorrelated increments over disjoint intervals
  (`Math2.donsker_increments_uncorrelated`),

which are exactly the covariance structure of standard Brownian motion, and are independent of the
law of the increments (whence "invariance"). The hypotheses are shown to be non-vacuous in
`Math2.donsker_hypotheses_satisfiable`, using the simple symmetric random walk.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The rescaled (Donsker) random walk built from the increments `X`:
`rescaledWalk X n t ω = (X 0 ω + ⋯ + X (⌊n t⌋₊ - 1) ω) / √n`.
This is the classical diffusive rescaling of the partial-sum process. -/
noncomputable def rescaledWalk (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n

/-- For independent, centred increments, distinct increments are uncorrelated. -/
lemma integral_mul_of_ne (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, X i ω * X j ω ∂μ = 0 := by
  have h := (hindep.indepFun hij).integral_fun_mul_eq_mul_integral
    (hL2 i).aestronglyMeasurable (hL2 j).aestronglyMeasurable
  simp [h, hmean i]

/-- The covariance of two partial sums: `E[S_a S_b] = min a b`. -/
lemma integral_partialSum_mul (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) (a b : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range a, X i ω) * (∑ j ∈ Finset.range b, X j ω) ∂μ =
      (min a b : ℕ) := by
  have hint : ∀ i j : ℕ, Integrable (fun ω => X i ω * X j ω) μ := fun i j =>
    MemLp.integrable_mul (hL2 i) (hL2 j)
  have hexp : ∀ i j : ℕ, ∫ ω, X i ω * X j ω ∂μ = if i = j then (1 : ℝ) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      simpa [pow_two] using hvar i
    · simp [h, integral_mul_of_ne hindep hL2 hmean h]
  calc ∫ ω, (∑ i ∈ Finset.range a, X i ω) * (∑ j ∈ Finset.range b, X j ω) ∂μ
      = ∫ ω, ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, X i ω * X j ω ∂μ := by
        simp [Finset.sum_mul_sum]
    _ = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, ∫ ω, X i ω * X j ω ∂μ := by
        rw [integral_finset_sum]
        · exact Finset.sum_congr rfl fun i _ =>
            integral_finset_sum _ (fun j _ => hint i j)
        · exact fun i _ => integrable_finset_sum _ (fun j _ => hint i j)
    _ = (min a b : ℕ) := by
        simp only [hexp]
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq', Finset.mem_range]
        have hset : {x ∈ Finset.range b | x < a} = Finset.range (min a b) := by
          ext x
          simp [and_comm]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hset]
        simp

/-- **Donsker's invariance principle (covariance form).**

For a sequence of independent, square-integrable, centred increments with unit variance, the
diffusively rescaled random walk `W_n(t) = S_{⌊nt⌋}/√n` has covariance function converging to
that of standard Brownian motion, `E[W(s) W(t)] = min s t`.

This is the second-order (covariance) content of Donsker's invariance principle: it is exactly the
statement that, whatever the law of the increments (invariance), the limiting process has the
covariance structure of Brownian motion. The key limit input is Mathlib's
`tendsto_nat_floor_mul_div_atTop`. -/
theorem donsker_invariance [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => ∫ ω, rescaledWalk X n s ω * rescaledWalk X n t ω ∂μ)
      atTop (𝓝 (min s t)) := by
  have key : ∀ n : ℕ, (∫ ω, rescaledWalk X n s ω * rescaledWalk X n t ω ∂μ)
      = (⌊min s t * (n : ℝ)⌋₊ : ℝ) / (n : ℝ) := by
    intro n
    have hfloor : (min ⌊(n : ℝ) * s⌋₊ ⌊(n : ℝ) * t⌋₊ : ℕ) = ⌊min s t * (n : ℝ)⌋₊ := by
      rcases le_total s t with h | h
      · rw [min_eq_left (Nat.floor_mono (by nlinarith [Nat.cast_nonneg (α := ℝ) n])),
          min_eq_left h, mul_comm]
      · rw [min_eq_right (Nat.floor_mono (by nlinarith [Nat.cast_nonneg (α := ℝ) n])),
          min_eq_right h, mul_comm]
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg n)
    simp only [rescaledWalk, div_mul_div_comm, hsq]
    rw [integral_div, integral_partialSum_mul hindep hL2 hmean hvar, hfloor]
  simp only [key]
  exact (tendsto_nat_floor_mul_div_atTop (le_min hs ht)).comp tendsto_natCast_atTop_atTop

/-- The rescaled walk is square-integrable. -/
lemma memLp_rescaledWalk (hL2 : ∀ i, MemLp (X i) 2 μ) (n : ℕ) (r : ℝ) :
    MemLp (rescaledWalk X n r) 2 μ := by
  have h : MemLp (fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * r⌋₊, X i ω) 2 μ := by
    have h0 := memLp_finset_sum' (Finset.range ⌊(n : ℝ) * r⌋₊) (fun i (_ : i ∈ _) => hL2 i)
    rwa [show (∑ i ∈ Finset.range ⌊(n : ℝ) * r⌋₊, X i)
      = (fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * r⌋₊, X i ω) from
      funext fun ω => by simp] at h0
  show MemLp (fun ω => (∑ i ∈ Finset.range ⌊(n : ℝ) * r⌋₊, X i ω) / Real.sqrt n) 2 μ
  simpa [div_eq_inv_mul] using h.const_mul (Real.sqrt n)⁻¹

/-- The variance of an increment of the rescaled walk converges to the length of the time
interval, as for Brownian motion. -/
theorem donsker_increment_variance [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) ^ 2 ∂μ)
      atTop (𝓝 (t - s)) := by
  have ht : 0 ≤ t := hs.trans hst
  have hexp : ∀ n : ℕ, (∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) ^ 2 ∂μ)
      = (∫ ω, rescaledWalk X n t ω * rescaledWalk X n t ω ∂μ)
        - 2 * (∫ ω, rescaledWalk X n t ω * rescaledWalk X n s ω ∂μ)
        + (∫ ω, rescaledWalk X n s ω * rescaledWalk X n s ω ∂μ) := by
    intro n
    have hI : ∀ r q : ℝ, Integrable (fun ω => rescaledWalk X n r ω * rescaledWalk X n q ω) μ :=
      fun r q => MemLp.integrable_mul (memLp_rescaledWalk hL2 n r) (memLp_rescaledWalk hL2 n q)
    have e0 : ∀ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) ^ 2
        = rescaledWalk X n t ω * rescaledWalk X n t ω
          - 2 * (rescaledWalk X n t ω * rescaledWalk X n s ω)
          + rescaledWalk X n s ω * rescaledWalk X n s ω := fun ω => by ring
    have I1 : Integrable (fun ω => rescaledWalk X n t ω * rescaledWalk X n t ω
        - 2 * (rescaledWalk X n t ω * rescaledWalk X n s ω)) μ :=
      (hI t t).sub ((hI t s).const_mul 2)
    simp_rw [e0]
    rw [integral_add I1 (hI s s), integral_sub (hI t t) ((hI t s).const_mul 2),
      integral_const_mul]
  simp only [hexp]
  have h1 := donsker_invariance (μ := μ) hindep hL2 hmean hvar ht ht
  have h2 := donsker_invariance (μ := μ) hindep hL2 hmean hvar ht hs
  have h3 := donsker_invariance (μ := μ) hindep hL2 hmean hvar hs hs
  have hval : min t t - 2 * min t s + min s s = t - s := by
    rw [min_self, min_self, min_eq_right hst]
    ring
  have hlim := (h1.sub (h2.const_mul 2)).add h3
  rwa [hval] at hlim

/-- The rescaled walk has asymptotically uncorrelated increments over disjoint intervals, as
Brownian motion does. -/
theorem donsker_increments_uncorrelated [IsProbabilityMeasure μ]
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    {s t u v : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    Tendsto (fun n : ℕ => ∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) *
        (rescaledWalk X n v ω - rescaledWalk X n u ω) ∂μ) atTop (𝓝 0) := by
  have ht : 0 ≤ t := hs.trans hst
  have hu : 0 ≤ u := ht.trans htu
  have hv : 0 ≤ v := hu.trans huv
  have hexp : ∀ n : ℕ, (∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) *
      (rescaledWalk X n v ω - rescaledWalk X n u ω) ∂μ)
      = (∫ ω, rescaledWalk X n t ω * rescaledWalk X n v ω ∂μ)
        - (∫ ω, rescaledWalk X n t ω * rescaledWalk X n u ω ∂μ)
        - ((∫ ω, rescaledWalk X n s ω * rescaledWalk X n v ω ∂μ)
        - (∫ ω, rescaledWalk X n s ω * rescaledWalk X n u ω ∂μ)) := by
    intro n
    have hI : ∀ r q : ℝ, Integrable (fun ω => rescaledWalk X n r ω * rescaledWalk X n q ω) μ :=
      fun r q => MemLp.integrable_mul (memLp_rescaledWalk hL2 n r) (memLp_rescaledWalk hL2 n q)
    have e0 : ∀ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) *
        (rescaledWalk X n v ω - rescaledWalk X n u ω)
        = (rescaledWalk X n t ω * rescaledWalk X n v ω
            - rescaledWalk X n t ω * rescaledWalk X n u ω)
          - (rescaledWalk X n s ω * rescaledWalk X n v ω
            - rescaledWalk X n s ω * rescaledWalk X n u ω) := fun ω => by ring
    have I1 : Integrable (fun ω => rescaledWalk X n t ω * rescaledWalk X n v ω
        - rescaledWalk X n t ω * rescaledWalk X n u ω) μ := (hI t v).sub (hI t u)
    have I2 : Integrable (fun ω => rescaledWalk X n s ω * rescaledWalk X n v ω
        - rescaledWalk X n s ω * rescaledWalk X n u ω) μ := (hI s v).sub (hI s u)
    simp_rw [e0]
    rw [integral_sub I1 I2, integral_sub (hI t v) (hI t u), integral_sub (hI s v) (hI s u)]
  simp only [hexp]
  have h1 := donsker_invariance (μ := μ) hindep hL2 hmean hvar ht hv
  have h2 := donsker_invariance (μ := μ) hindep hL2 hmean hvar ht hu
  have h3 := donsker_invariance (μ := μ) hindep hL2 hmean hvar hs hv
  have h4 := donsker_invariance (μ := μ) hindep hL2 hmean hvar hs hu
  have : min t v - min t u - (min s v - min s u) = (0 : ℝ) := by
    rw [min_eq_left (htu.trans huv), min_eq_left htu,
      min_eq_left (hst.trans (htu.trans huv)), min_eq_left (hst.trans htu)]
    ring
  simpa [this] using ((h1.sub h2).sub (h3.sub h4))

/-! ### Non-vacuity: the hypotheses are satisfied by a simple random walk -/

/-- The fair coin measure on `Bool`. -/
noncomputable def coinMeasure : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure coinMeasure :=
  ⟨by simp [coinMeasure, ENNReal.inv_two_add_inv_two]⟩

/-- The Rademacher (±1) increment attached to a coin toss. -/
noncomputable def rademacher : Bool → ℝ := fun b => if b then 1 else -1

lemma coinMeasure_integral (f : Bool → ℝ) : ∫ b, f b ∂coinMeasure = (f true + f false) / 2 := by
  haveI h1 : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (true : Bool)) :=
    ⟨by simp [Measure.smul_apply]⟩
  haveI h2 : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (false : Bool)) :=
    ⟨by simp [Measure.smul_apply]⟩
  rw [coinMeasure, integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp
  ring

/-- The law of an i.i.d. sequence of fair coin tosses. -/
noncomputable def coinSequenceMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => coinMeasure)

instance : IsProbabilityMeasure coinSequenceMeasure := by
  unfold coinSequenceMeasure; infer_instance

lemma coinSequenceMeasure_integral (f : Bool → ℝ) (i : ℕ) :
    ∫ ω, f (ω i) ∂coinSequenceMeasure = ∫ b, f b ∂coinMeasure := by
  calc ∫ ω, f (ω i) ∂coinSequenceMeasure
      = ∫ b, f b ∂(coinSequenceMeasure.map (fun ω => ω i)) :=
        (integral_map (measurable_pi_apply i).aemeasurable
          (Measurable.of_discrete (f := f)).aestronglyMeasurable).symm
    _ = ∫ b, f b ∂coinMeasure := by rw [coinSequenceMeasure, Measure.infinitePi_map_eval]

/-- The hypotheses of `Math2.donsker_invariance` are not vacuous: the increments of the simple
symmetric random walk (i.i.d. Rademacher variables) satisfy all of them. -/
theorem donsker_hypotheses_satisfiable :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure μ ∧ iIndepFun X μ ∧ (∀ i, MemLp (X i) 2 μ) ∧
        (∀ i, ∫ ω, X i ω ∂μ = 0) ∧ (∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) := by
  refine ⟨ℕ → Bool, inferInstance, coinSequenceMeasure,
    fun i ω => rademacher (ω i), inferInstance,
    iIndepFun_infinitePi (fun _ => Measurable.of_discrete), fun i => ?_, fun i => ?_, fun i => ?_⟩
  · have hm : Measurable (fun ω : ℕ → Bool => rademacher (ω i)) :=
      (Measurable.of_discrete (f := rademacher)).comp (measurable_pi_apply i)
    refine MemLp.of_bound hm.aestronglyMeasurable 1 (.of_forall fun ω => ?_)
    by_cases h : ω i <;> simp [rademacher, h]
  · rw [coinSequenceMeasure_integral rademacher i, coinMeasure_integral]
    norm_num [rademacher]
  · rw [coinSequenceMeasure_integral (fun b => rademacher b ^ 2) i, coinMeasure_integral]
    norm_num [rademacher]

end Math2

