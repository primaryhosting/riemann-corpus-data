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

import Mathlib

/-!
# Equidistribution of multiples, and the reduction of the divisor summatory function
to its main term

This file carries out a "level of distribution" style reduction for the simplest possible
sequence, the sequence of all integers, and deduces from it the leading-order asymptotics of
the divisor summatory function.

For a modulus `q`, the number of `n ∈ [1, N]` lying in the residue class `0 mod q` is
`N / q + O(1)` (`abs_countMultiples_sub_le`).  Summing this equidistribution statement over all
moduli `q ≤ N` (a total error of size `O(N)`, `abs_totalCount_sub_harmonic_le`) turns the
"total" count

  `totalCount N = ∑_{n ≤ N} d(n) = ∑_{q ≤ N} #{n ≤ N : q ∣ n}`

into its main term `N * H_N`, where `H_N` is the `N`-th harmonic number.  Since `H_N ∼ log N`,
this gives the Dirichlet asymptotic

  `∑_{n ≤ N} d(n) ∼ N log N`,

which is the statement `total_over_main_tendsto`.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of integers `n ∈ [1, N]` that are divisible by `q`, i.e. the number of
elements of `[1, N]` in the residue class `0 mod q`. -/
def countMultiples (N q : ℕ) : ℕ := #{n ∈ Finset.Icc 1 N | q ∣ n}

/-- The total count: the divisor summatory function `∑_{n ≤ N} d(n)`. -/
def totalCount (N : ℕ) : ℕ := ∑ n ∈ Finset.Icc 1 N, n.divisors.card

/-- The predicted main term `N log N` for `totalCount N`. -/
noncomputable def mainTerm (N : ℕ) : ℝ := N * Real.log N

/-- Exact evaluation of the counting function of multiples. -/
lemma countMultiples_eq_div (N q : ℕ) : countMultiples N q = N / q := by
  rw [countMultiples, ← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1

/-- Equidistribution with error `O(1)`: the number of `n ≤ N` in the class `0 mod q` differs
from the expected count `N / q` by at most `1`. -/
lemma abs_countMultiples_sub_le (N q : ℕ) (hq : 1 ≤ q) :
    |(countMultiples N q : ℝ) - (N : ℝ) / q| ≤ 1 := by
  rw [countMultiples_eq_div]
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hmod : (N:ℝ) = q * ((N / q : ℕ) : ℝ) + ((N % q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N q).symm
  have hlt : ((N % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt _ hq
  have hnn : (0:ℝ) ≤ ((N % q : ℕ) : ℝ) := by positivity
  have hdiv : (N:ℝ) / q = ((N / q : ℕ) : ℝ) + ((N % q : ℕ) : ℝ) / q := by
    field_simp
    linarith [hmod]
  rw [hdiv, abs_le]
  constructor
  · have : ((N % q : ℕ) : ℝ) / q ≤ 1 := by rw [div_le_one hq0]; linarith
    linarith
  · have : (0:ℝ) ≤ ((N % q : ℕ) : ℝ) / q := by positivity
    linarith

/-- The total count is the sum over moduli `q ≤ N` of the counts of multiples of `q`. -/
lemma totalCount_eq_sum_countMultiples (N : ℕ) :
    totalCount N = ∑ q ∈ Finset.Icc 1 N, countMultiples N q := by
  have key : ∀ n ∈ Finset.Icc 1 N, n.divisors = {q ∈ Finset.Icc 1 N | q ∣ n} := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    ext q
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, hne⟩
      exact ⟨⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hdvd; omega),
        le_trans (Nat.le_of_dvd (by omega) hdvd) hn.2⟩, hdvd⟩
    · rintro ⟨-, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [totalCount, Finset.sum_congr rfl (fun n hn => by rw [key n hn])]
  simp only [countMultiples, Finset.card_filter]
  exact Finset.sum_comm

/-- Summing the equidistribution statement over all moduli `q ≤ N`: the total count agrees
with `N * H_N` up to an error of size at most `N`. -/
lemma abs_totalCount_sub_harmonic_le (N : ℕ) :
    |(totalCount N : ℝ) - N * (harmonic N : ℝ)| ≤ N := by
  have hcast : ((totalCount N : ℕ) : ℝ) = ∑ q ∈ Finset.Icc 1 N, ((countMultiples N q : ℕ) : ℝ) := by
    rw [totalCount_eq_sum_countMultiples]
    push_cast
    ring
  have hH : ((harmonic N : ℚ) : ℝ) = ∑ q ∈ Finset.Icc 1 N, ((q : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    ring
  rw [hcast, hH, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ q ∈ Finset.Icc 1 N, ((countMultiples N q : ℝ) - N * (q : ℝ)⁻¹)|
      ≤ ∑ q ∈ Finset.Icc 1 N, |(countMultiples N q : ℝ) - N * (q : ℝ)⁻¹| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ Finset.Icc 1 N, 1 := by
        refine Finset.sum_le_sum ?_
        intro q hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
        have := abs_countMultiples_sub_le N q hq1
        rwa [div_eq_mul_inv] at this
    _ = N := by simp

/-- The harmonic numbers are asymptotic to the logarithm: `H_N / log N → 1`. -/
lemma harmonic_div_log_tendsto :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun N : ℕ => 1 / Real.log N) atTop (𝓝 0) := by
    simpa [one_div, Function.comp] using tendsto_inv_atTop_zero.comp hlog
  have hinv : Tendsto (fun N : ℕ => 1 + 1 / Real.log N) atTop (𝓝 1) := by
    simpa using h0.const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
  · filter_upwards [hlog.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN hN1
    rw [le_div_iff₀ hN]
    have h1 : Real.log ((N : ℝ) + 1) ≤ (harmonic N : ℝ) := by
      have := log_add_one_le_harmonic N
      push_cast at this
      exact this
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
    have h2 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hNpos (by linarith)
    linarith
  · filter_upwards [hlog.eventually_gt_atTop 0] with N hN
    rw [div_le_iff₀ hN]
    have h1 : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
    have h3 : (1 + 1 / Real.log N) * Real.log N = Real.log N + 1 := by field_simp
    linarith

/-- The reduction step: given the asymptotics of the harmonic numbers, the total count is
asymptotic to its main term. -/
theorem total_over_main_tendsto_of_harmonic
    (hHarm : Tendsto (fun N : ℕ => (harmonic N : ℝ) / Real.log N) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => (totalCount N : ℝ) / mainTerm N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun N : ℕ => 1 / Real.log N) atTop (𝓝 0) := by
    simpa [one_div, Function.comp] using tendsto_inv_atTop_zero.comp hlog
  set B : ℕ → ℝ := fun N => ((totalCount N : ℝ) - N * (harmonic N : ℝ)) / ((N : ℝ) * Real.log N)
    with hBdef
  have hBtend : Tendsto B atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [hlog.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN hN1
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
    rw [Real.norm_eq_abs, hBdef]
    simp only [abs_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have habs : |(N : ℝ) * Real.log N| = (N : ℝ) * Real.log N := abs_of_pos (by positivity)
    rw [habs]
    nlinarith [abs_totalCount_sub_harmonic_le N, hN, hNpos]
  have hsum := hHarm.add hBtend
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  rw [hBdef, mainTerm]
  field_simp
  ring

/-- **Dirichlet's asymptotic for the divisor summatory function** (leading order):
`(∑_{n ≤ N} d(n)) / (N log N) → 1`. -/
theorem total_over_main_tendsto :
    Tendsto (fun N : ℕ => (totalCount N : ℝ) / mainTerm N) atTop (𝓝 1) :=
  total_over_main_tendsto_of_harmonic harmonic_div_log_tendsto

end EquidistributionBVReduction
end Brockian

