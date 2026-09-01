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
# Weighted Weyl bridge for Liouville correlation

This module proves an **analytic transfer theorem**: for a bounded complex weight `w`
and an arbitrary real sequence `x`, vanishing of the weighted Weyl sums against *every*
Fourier mode `fourier k` (including the trivial mode `k = 0`) forces vanishing of the
weighted averages against *every* continuous observable on the circle `𝕋 = AddCircle 1`.

The point of the module is to isolate the genuinely open arithmetic input.  Nothing here
proves any cancellation for the Liouville function: the Fourier cancellation is carried as
an *explicit hypothesis* in every statement below.

## Status labels

* `Frontier.Spectral.weighted_weyl_correlation` — **STANDARD**: a kernel-verified,
  unconditional theorem of functional analysis (density of the Fourier span in
  `C(𝕋, ℂ)` plus a uniform `‖·‖ ≤ 1` bound, via a `3ε` argument).
* `Frontier.Spectral.liouville_continuous_correlation_of_fourier` — **CONDITIONAL**:
  the Fourier-cancellation input `hfourier` is an explicit, unproved hypothesis.  This is
  *not* a proof of Chowla's conjecture, of Sarnak's conjecture, or of any unconditional
  decorrelation statement for `λ(n)`.
-/
import Mathlib

open Filter Topology Finset Submodule Set

noncomputable section

namespace Frontier.Spectral

/-- The circle `𝕋 = ℝ / ℤ`, realised as `AddCircle (1 : ℝ)`. -/
abbrev Torus : Type := AddCircle (1 : ℝ)

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The weighted Weyl average
`weightedAvg w x F N = N⁻¹ * ∑_{n < N} w n * F (x n mod 1)`. -/
def weightedAvg (w : ℕ → ℂ) (x : ℕ → ℝ) (F : C(Torus, ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, w n * F ((x n : ℝ) : Torus)

section Generic

variable {w : ℕ → ℂ} {x : ℕ → ℝ}

@[simp] lemma weightedAvg_zero_fun (N : ℕ) : weightedAvg w x 0 N = 0 := by
  simp [weightedAvg]

lemma weightedAvg_add (F G : C(Torus, ℂ)) (N : ℕ) :
    weightedAvg w x (F + G) N = weightedAvg w x F N + weightedAvg w x G N := by
  simp only [weightedAvg, ContinuousMap.add_apply, mul_add, Finset.sum_add_distrib]

lemma weightedAvg_smul (c : ℂ) (F : C(Torus, ℂ)) (N : ℕ) :
    weightedAvg w x (c • F) N = c * weightedAvg w x F N := by
  have h : ∑ n ∈ Finset.range N, w n * (c • F) ((x n : ℝ) : Torus)
      = c * ∑ n ∈ Finset.range N, w n * F ((x n : ℝ) : Torus) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [weightedAvg, weightedAvg, h]
  ring

lemma weightedAvg_sub (F G : C(Torus, ℂ)) (N : ℕ) :
    weightedAvg w x (F - G) N = weightedAvg w x F N - weightedAvg w x G N := by
  simp only [weightedAvg, ContinuousMap.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- **Uniform bound.** If the weight is bounded by `1` in absolute value, then every
weighted average is bounded by the sup-norm of the observable. -/
theorem norm_weightedAvg_le (hw : ∀ n, ‖w n‖ ≤ 1) (F : C(Torus, ℂ)) (N : ℕ) :
    ‖weightedAvg w x F N‖ ≤ ‖F‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [weightedAvg]
  have hFnn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg F
  have hsum : ‖∑ n ∈ Finset.range N, w n * F ((x n : ℝ) : Torus)‖ ≤ (N : ℝ) * ‖F‖ := by
    calc ‖∑ n ∈ Finset.range N, w n * F ((x n : ℝ) : Torus)‖
        ≤ ∑ n ∈ Finset.range N, ‖w n * F ((x n : ℝ) : Torus)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ‖F‖ := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul]
          calc ‖w n‖ * ‖F ((x n : ℝ) : Torus)‖ ≤ 1 * ‖F‖ := by
                exact mul_le_mul (hw n) (F.norm_coe_le_norm _) (norm_nonneg _) zero_le_one
            _ = ‖F‖ := one_mul _
      _ = (N : ℝ) * ‖F‖ := by simp
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [weightedAvg, norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hNpos]
  linarith [hsum]

/-- Vanishing of the weighted averages propagates from the Fourier modes to their
linear span. -/
theorem tendsto_weightedAvg_of_mem_span
    (hfourier : ∀ k : ℤ, Tendsto (weightedAvg w x (fourier k)) atTop (𝓝 0))
    {F : C(Torus, ℂ)} (hF : F ∈ span ℂ (Set.range (fun k : ℤ => fourier (T := 1) k))) :
    Tendsto (weightedAvg w x F) atTop (𝓝 0) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨k, rfl⟩ := hF
      exact hfourier k
  | zero =>
      have heq : weightedAvg w x 0 = fun _ : ℕ => (0 : ℂ) := funext fun N => weightedAvg_zero_fun N
      rw [heq]
      exact tendsto_const_nhds
  | add F G _ _ hF hG =>
      have heq : weightedAvg w x (F + G) = fun N => weightedAvg w x F N + weightedAvg w x G N :=
        funext fun N => weightedAvg_add F G N
      rw [heq]
      simpa using hF.add hG
  | smul c F _ hF =>
      have heq : weightedAvg w x (c • F) = fun N => c * weightedAvg w x F N :=
        funext fun N => weightedAvg_smul c F N
      rw [heq]
      simpa using hF.const_mul c

/-- **STANDARD (unconditional).**  Weighted Weyl bridge: for a weight bounded by `1`,
vanishing of the weighted Weyl sums along every Fourier mode `fourier k`, `k : ℤ`
(including `k = 0`), implies vanishing of the weighted averages against every continuous
observable `F : C(𝕋, ℂ)`.

The proof combines the uniform bound `norm_weightedAvg_le` with the density of the span
of the Fourier monomials in `C(𝕋, ℂ)` (`span_fourier_closure_eq_top`) in a `3ε`
argument. -/
theorem weighted_weyl_correlation {w : ℕ → ℂ} {x : ℕ → ℝ}
    (hw : ∀ n, ‖w n‖ ≤ 1)
    (hfourier : ∀ k : ℤ, Tendsto (weightedAvg w x (fourier k)) atTop (𝓝 0))
    (F : C(Torus, ℂ)) :
    Tendsto (weightedAvg w x F) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- density of the Fourier span
  have hmem : F ∈ (span ℂ (Set.range (fun k : ℤ => fourier (T := 1) k))).topologicalClosure := by
    rw [span_fourier_closure_eq_top (T := 1)]
    trivial
  have hclosure : F ∈ closure ((span ℂ (Set.range (fun k : ℤ => fourier (T := 1) k))) : Set _) :=
    hmem
  obtain ⟨G, hGmem, hGdist⟩ := Metric.mem_closure_iff.mp hclosure (ε / 3) (by linarith)
  have hGtend := tendsto_weightedAvg_of_mem_span hfourier hGmem
  rw [Metric.tendsto_atTop] at hGtend
  obtain ⟨M, hM⟩ := hGtend (ε / 3) (by linarith)
  refine ⟨M, fun n hn => ?_⟩
  have hMn := hM n hn
  rw [dist_eq_norm, sub_zero] at hMn ⊢
  have hsplit : weightedAvg w x F n
      = weightedAvg w x (F - G) n + weightedAvg w x G n := by
    rw [weightedAvg_sub]; ring
  have hbound : ‖weightedAvg w x (F - G) n‖ ≤ ‖F - G‖ := norm_weightedAvg_le hw _ _
  have hFG : ‖F - G‖ < ε / 3 := by
    rw [← dist_eq_norm]; exact hGdist
  calc ‖weightedAvg w x F n‖
      ≤ ‖weightedAvg w x (F - G) n‖ + ‖weightedAvg w x G n‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ < ε / 3 + ε / 3 := by
        exact add_lt_add (hbound.trans_lt hFG) hMn
    _ < ε := by linarith

end Generic

/-! ### The Liouville specialization

Mathlib (at the pinned version) has no canonical Liouville arithmetic function, so we
define it from prime-factor multiplicity in the standard way, using Mathlib's
`ArithmeticFunction.cardFactors` (the function `Ω`, counting prime factors with
multiplicity):
`λ(n) = (-1)^{Ω(n)}`.  This is the classical Liouville function; the lemmas below record
that it is unimodular, completely multiplicative, and takes the value `-1` at primes, so
it cannot be mistaken for an arbitrary unconstrained weight. -/

/-- The Liouville function `λ(n) = (-1)^{Ω(n)}`, valued in `ℂ`, where `Ω = cardFactors`
counts prime factors with multiplicity. -/
def liouvilleWeight (n : ℕ) : ℂ := (-1) ^ (ArithmeticFunction.cardFactors n)

lemma liouvilleWeight_apply (n : ℕ) :
    liouvilleWeight n = (-1) ^ (n.primeFactorsList.length) := by
  rw [liouvilleWeight, ArithmeticFunction.cardFactors_apply]

@[simp] lemma liouvilleWeight_one : liouvilleWeight 1 = 1 := by
  simp [liouvilleWeight]

lemma liouvilleWeight_prime {p : ℕ} (hp : p.Prime) : liouvilleWeight p = -1 := by
  rw [liouvilleWeight, ArithmeticFunction.cardFactors_apply_prime hp, pow_one]

/-- Complete multiplicativity of the Liouville function. -/
lemma liouvilleWeight_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    liouvilleWeight (m * n) = liouvilleWeight m * liouvilleWeight n := by
  rw [liouvilleWeight, liouvilleWeight, liouvilleWeight,
    ArithmeticFunction.cardFactors_mul hm hn, pow_add]

/-- The Liouville function is unimodular: `|λ(n)| = 1`.  In particular `|λ(n)| = 1` for every
positive integer `n` (the positivity hypothesis turns out to be unnecessary here, because
`Ω 0 = 0` in Mathlib's convention, so `λ 0 = 1`). -/
lemma norm_liouvilleWeight (n : ℕ) : ‖liouvilleWeight n‖ = 1 := by
  rw [liouvilleWeight, norm_pow, norm_neg, norm_one, one_pow]

lemma norm_liouvilleWeight_le (n : ℕ) : ‖liouvilleWeight n‖ ≤ 1 :=
  (norm_liouvilleWeight n).le

/-- **CONDITIONAL.**  Liouville specialization of the weighted Weyl bridge.

*Hypothesis* `hfourier` is the genuinely open arithmetic input: cancellation of the
Liouville-weighted Weyl sums along every Fourier mode `fourier k` (`k : ℤ`, including
`k = 0`, which is the prime-number-theorem-type input `N⁻¹ ∑_{n<N} λ(n) → 0`).  It is
assumed here, not proved.

*Conclusion*: the Liouville-weighted averages then vanish against every continuous
observable on the circle.

This statement is therefore **not** a proof of Chowla's or Sarnak's conjecture, nor of
any unconditional decorrelation theorem for `λ(n)`. -/
theorem liouville_continuous_correlation_of_fourier {x : ℕ → ℝ}
    (hfourier : ∀ k : ℤ, Tendsto (weightedAvg liouvilleWeight x (fourier k)) atTop (𝓝 0))
    (F : C(Torus, ℂ)) :
    Tendsto (weightedAvg liouvilleWeight x F) atTop (𝓝 0) :=
  weighted_weyl_correlation norm_liouvilleWeight_le hfourier F

end Frontier.Spectral

#print axioms Frontier.Spectral.weighted_weyl_correlation
#print axioms Frontier.Spectral.liouville_continuous_correlation_of_fourier

