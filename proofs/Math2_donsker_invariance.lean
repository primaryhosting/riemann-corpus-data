import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Nat Classical Topology ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory

set_option maxHeartbeats 1000000

namespace Math2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The random walk with steps `X`: `walk X n = ∑_{i < n} X i`. -/
noncomputable def walk (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range n, X i ω

@[simp] lemma walk_zero (X : ℕ → Ω → ℝ) (ω : Ω) : walk X 0 ω = 0 := by simp [walk]

/-- The rescaled (Donsker) random walk `W n t = S_{⌊n t⌋} / √n`. -/
noncomputable def rescaledWalk (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  walk X ⌊(n : ℝ) * t⌋₊ ω / Real.sqrt n

/-- A sequence of (deterministic) constants converging to `c₀` converges in probability to `c₀`. -/
lemma tendstoInMeasure_const_of_tendsto {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) :
    TendstoInMeasure μ (fun n (_ : Ω) ↦ c n) atTop (fun _ ↦ c₀) :=
  tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
    (Filter.Eventually.of_forall fun _ ↦ hc)

/-- Convergence in distribution passes to subsequences indexed by any map tending to infinity. -/
lemma tendstoInDistribution_comp_atTop {X : ℕ → Ω → ℝ} {Z : Ω → ℝ}
    (h : TendstoInDistribution X atTop Z μ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) :
    TendstoInDistribution (fun n ↦ X (k n)) atTop Z μ where
  forall_aemeasurable n := h.forall_aemeasurable (k n)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hk

/-- If `Z` is standard Gaussian, then `√t * Z` has the Gaussian law with variance `t`,
i.e. the law of Brownian motion at time `t`. -/
lemma map_sqrt_mul_gaussian {Z : Ω → ℝ} (hZmeas : AEMeasurable Z μ)
    (hZ : μ.map Z = gaussianReal 0 1) {t : ℝ} (ht : 0 ≤ t) :
    μ.map (fun ω ↦ Real.sqrt t * Z ω) = gaussianReal 0 t.toNNReal := by
  have h1 : μ.map (fun ω ↦ Real.sqrt t * Z ω)
      = (μ.map Z).map (fun x ↦ Real.sqrt t * x) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZmeas]
    rfl
  have hsq : (⟨Real.sqrt t ^ 2, by positivity⟩ : ℝ≥0) = t.toNNReal := by
    ext
    simp [Real.sq_sqrt ht, Real.coe_toNNReal _ ht]
  rw [h1, hZ, gaussianReal_map_const_mul]
  simp [← hsq]

/-- `⌊n t⌋ → ∞` when `t > 0`. -/
lemma tendsto_floor_mul_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ ⌊(n : ℝ) * t⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const ht)

/-- `⌊n t⌋ / n → t`. -/
lemma tendsto_floor_mul_div {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ (⌊(n : ℝ) * t⌋₊ : ℝ) / n) atTop (𝓝 t) := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simpa using tendsto_const_nhds (α := ℝ) (f := atTop (α := ℕ)) (a := (0 : ℝ))
  · have h1 : Tendsto (fun n : ℕ ↦ (⌊(n : ℝ) * t⌋₊ : ℝ) / ((n : ℝ) * t)) atTop (𝓝 1) :=
      tendsto_nat_floor_div_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const ht')
    have h2 := h1.mul_const t
    rw [one_mul] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp

/-- The scaling factors `√⌊n t⌋ / √n` converge to `√t`. -/
lemma tendsto_sqrt_floor_div {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ Real.sqrt (⌊(n : ℝ) * t⌋₊) / Real.sqrt n) atTop
      (𝓝 (Real.sqrt t)) := by
  have h := (Real.continuous_sqrt.tendsto t).comp (tendsto_floor_mul_div ht)
  refine h.congr fun n ↦ ?_
  simp [Function.comp_apply, Real.sqrt_div' _ (Nat.cast_nonneg n)]

/-- The rescaled walk factorises as a scaling factor times a CLT-normalised partial sum. -/
lemma rescaledWalk_eq (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) :
    rescaledWalk X n t ω
      = (Real.sqrt (⌊(n : ℝ) * t⌋₊) / Real.sqrt n)
          * (walk X ⌊(n : ℝ) * t⌋₊ ω / Real.sqrt (⌊(n : ℝ) * t⌋₊)) := by
  set k := ⌊(n : ℝ) * t⌋₊ with hk
  have hL : rescaledWalk X n t ω = walk X k ω / Real.sqrt n := rfl
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hL, hk0]
    simp
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
    have hsk : Real.sqrt (k : ℝ) ≠ 0 := by positivity
    rw [hL]
    field_simp

/-- **Donsker's invariance principle** (marginal / one-time form).

Let `X` be the steps of a random walk on a probability space `(Ω, μ)`, with partial sums
`S n = walk X n = ∑_{i < n} X i`, and assume the central limit theorem for these steps:
`S n / √n` converges in distribution to a standard Gaussian random variable `Z`.

Then for every time `t ≥ 0` the rescaled walk `W n t = S_{⌊n t⌋} / √n` converges in distribution
to `√t · Z`, and the law of `√t · Z` is `N(0, t)`, the law of Brownian motion at time `t`. -/
theorem donsker_invariance {X : ℕ → Ω → ℝ} {Z : Ω → ℝ}
    (hZ : μ.map Z = gaussianReal 0 1)
    (hCLT : TendstoInDistribution (fun n ω ↦ walk X n ω / Real.sqrt n) atTop Z μ)
    {t : ℝ} (ht : 0 ≤ t) :
    TendstoInDistribution (fun n ↦ rescaledWalk X n t) atTop (fun ω ↦ Real.sqrt t * Z ω) μ
      ∧ μ.map (fun ω ↦ Real.sqrt t * Z ω) = gaussianReal 0 t.toNNReal := by
  have hZmeas : AEMeasurable Z μ := hCLT.aemeasurable_limit
  refine ⟨?_, map_sqrt_mul_gaussian hZmeas hZ ht⟩
  rcases eq_or_lt_of_le ht with rfl | ht'
  · -- Time `0`: both the rescaled walk and the limit are identically zero.
    have hfun : (fun n ↦ rescaledWalk X n (0 : ℝ)) = fun (_ : ℕ) (ω : Ω) ↦
        Real.sqrt (0 : ℝ) * Z ω := by
      funext n ω
      simp [rescaledWalk]
    rw [hfun]
    exact tendstoInDistribution_const (by simp)
  · -- Positive time: Slutsky applied to the subsequence `⌊n t⌋` of the CLT.
    have hsub : TendstoInDistribution
        (fun n ω ↦ walk X ⌊(n : ℝ) * t⌋₊ ω / Real.sqrt (⌊(n : ℝ) * t⌋₊)) atTop Z μ :=
      tendstoInDistribution_comp_atTop hCLT (tendsto_floor_mul_atTop ht')
    have hconst : TendstoInMeasure μ
        (fun (n : ℕ) (_ : Ω) ↦ Real.sqrt (⌊(n : ℝ) * t⌋₊) / Real.sqrt n) atTop
        (fun _ ↦ Real.sqrt t) :=
      tendstoInMeasure_const_of_tendsto (tendsto_sqrt_floor_div ht)
    have hslutsky := hsub.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ ↦ p.2 * p.1) (by fun_prop) hconst (fun _ ↦ aemeasurable_const)
    have hfun : (fun n ↦ rescaledWalk X n t) = fun (n : ℕ) (ω : Ω) ↦
        (Real.sqrt (⌊(n : ℝ) * t⌋₊) / Real.sqrt n)
          * (walk X ⌊(n : ℝ) * t⌋₊ ω / Real.sqrt (⌊(n : ℝ) * t⌋₊)) := by
      funext n ω
      exact rescaledWalk_eq X n t ω
    rw [hfun]
    exact hslutsky

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

