/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The singular series considered here is the Hardy–Littlewood twin-prime singular series
(without the leading factor `2`),
`𝔖 = ∏_{p odd prime} (1 - 1/(p-1)^2)`,
realised as the limit of its truncations `𝔖(N) = ∏_{p < N, p odd prime} (1 - 1/(p-1)^2)`.

The main result `Brockian.SingularSeriesConvergenceRate` is an *effective* convergence rate:
for every `N ≥ 3`,
`|𝔖(N) - 𝔖| ≤ 1/(N-2)`.
-/

namespace Brockian

open Finset

/-- The local factor at `p`: `1 - 1/(p-1)^2` at odd primes, and `1` at all other naturals. -/
noncomputable def localFactor (p : ℕ) : ℝ :=
  if p.Prime ∧ p ≠ 2 then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

/-- The truncated singular series `𝔖(N) = ∏_{p < N} (1 - 1/(p-1)^2)`, the product being over
odd primes `p < N`. -/
noncomputable def partialProduct (N : ℕ) : ℝ := ∏ p ∈ Finset.range N, localFactor p

/-- The singular series `𝔖 = ∏_{p odd prime} (1 - 1/(p-1)^2)`, defined as the infimum of its
(decreasing) truncations. -/
noncomputable def singularSeries : ℝ := ⨅ N : ℕ, partialProduct N

/-! ### Elementary bounds on the local factors -/

lemma three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  omega

lemma localFactor_le_one (p : ℕ) : localFactor p ≤ 1 := by
  unfold localFactor
  split
  · have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · exact le_rfl

lemma three_quarters_le_localFactor (p : ℕ) : (3 : ℝ) / 4 ≤ localFactor p := by
  unfold localFactor
  split
  · rename_i h
    have hp3 : 3 ≤ p := three_le_of_prime_ne_two h.1 h.2
    have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hx : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have h4 : (0 : ℝ) < 4 := by norm_num
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le h4 hx
    linarith
  · norm_num

lemma localFactor_nonneg (p : ℕ) : 0 ≤ localFactor p :=
  le_trans (by norm_num) (three_quarters_le_localFactor p)

/-- The complementary weight `1 - localFactor p` is nonnegative. -/
lemma one_sub_localFactor_nonneg (p : ℕ) : 0 ≤ 1 - localFactor p := by
  have := localFactor_le_one p; linarith

/-- For `p ≥ 3`, the weight `1 - localFactor p` is dominated by a telescoping quantity. -/
lemma one_sub_localFactor_le_telescope {p : ℕ} (hp : 3 ≤ p) :
    1 - localFactor p ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have key : 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
    field_simp
    ring
  rw [key]
  unfold localFactor
  split
  · have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    linarith
  · have : (0 : ℝ) < 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by positivity
    linarith

/-! ### A Weierstrass-type product inequality -/

lemma one_sub_sum_le_prod_one_sub {s : Finset ℕ} {a : ℕ → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      have hx0 : 0 ≤ a x := h0 x (Finset.mem_insert_self x s)
      have hx1 : a x ≤ 1 := h1 x (Finset.mem_insert_self x s)
      have h0' : ∀ i ∈ s, 0 ≤ a i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1' : ∀ i ∈ s, a i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have ihs := ih h0' h1'
      have hsum : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg h0'
      rw [Finset.prod_insert hx, Finset.sum_insert hx]
      nlinarith [ihs, hsum, hx0, hx1]

/-! ### Basic properties of the truncations -/

lemma partialProduct_nonneg (N : ℕ) : 0 ≤ partialProduct N :=
  Finset.prod_nonneg fun i _ => localFactor_nonneg i

lemma partialProduct_le_one (N : ℕ) : partialProduct N ≤ 1 :=
  Finset.prod_le_one (fun i _ => localFactor_nonneg i) (fun i _ => localFactor_le_one i)

lemma partialProduct_antitone : Antitone partialProduct := by
  intro M N hMN
  unfold partialProduct
  rw [← Finset.prod_range_mul_prod_Ico localFactor hMN]
  nlinarith [Finset.prod_nonneg (fun i (_ : i ∈ Finset.range M) => localFactor_nonneg i),
    Finset.prod_le_one (s := Finset.Ico M N) (fun i _ => localFactor_nonneg i)
      (fun i _ => localFactor_le_one i),
    Finset.prod_nonneg (fun i (_ : i ∈ Finset.Ico M N) => localFactor_nonneg i)]

lemma partialProduct_bddBelow : BddBelow (Set.range partialProduct) := by
  refine ⟨0, ?_⟩
  rintro x ⟨N, rfl⟩
  exact partialProduct_nonneg N

/-- The truncations converge to the singular series. -/
theorem tendsto_partialProduct :
    Filter.Tendsto partialProduct Filter.atTop (nhds singularSeries) :=
  tendsto_atTop_ciInf partialProduct_antitone partialProduct_bddBelow

/-! ### The tail estimate -/

/-- The total weight removed between levels `N` and `M` telescopes. -/
lemma sum_one_sub_localFactor_le {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    ∑ p ∈ Finset.Ico N M, (1 - localFactor p) ≤ 1 / ((N : ℝ) - 2) - 1 / ((M : ℝ) - 2) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      have hM3 : 3 ≤ M := le_trans hN hNM
      have hM : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
      rw [Finset.sum_Ico_succ_top hNM]
      have hstep := one_sub_localFactor_le_telescope hM3
      have hcast : ((M + 1 : ℕ) : ℝ) - 2 = (M : ℝ) - 1 := by push_cast; ring
      rw [hcast]
      linarith

lemma partialProduct_lower_bound {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    partialProduct N * (1 - 1 / ((N : ℝ) - 2)) ≤ partialProduct M := by
  have hN' : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsplit : partialProduct M
      = partialProduct N * ∏ p ∈ Finset.Ico N M, localFactor p := by
    unfold partialProduct
    rw [Finset.prod_range_mul_prod_Ico localFactor hNM]
  have hweier : 1 - ∑ p ∈ Finset.Ico N M, (1 - localFactor p)
      ≤ ∏ p ∈ Finset.Ico N M, (1 - (1 - localFactor p)) := by
    refine one_sub_sum_le_prod_one_sub (fun i _ => one_sub_localFactor_nonneg i) ?_
    intro i _
    have := localFactor_nonneg i
    linarith
  have hsimp : ∏ p ∈ Finset.Ico N M, (1 - (1 - localFactor p))
      = ∏ p ∈ Finset.Ico N M, localFactor p := by
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [hsimp] at hweier
  have htail := sum_one_sub_localFactor_le hN hNM
  have hMpos : (0 : ℝ) ≤ 1 / ((M : ℝ) - 2) := by
    have hM : (3 : ℝ) ≤ (M : ℝ) := by
      have : 3 ≤ M := le_trans hN hNM
      exact_mod_cast this
    exact div_nonneg zero_le_one (by linarith)
  have hlow : 1 - 1 / ((N : ℝ) - 2) ≤ ∏ p ∈ Finset.Ico N M, localFactor p := by
    linarith
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hlow (partialProduct_nonneg N)

lemma singularSeries_le (N : ℕ) : singularSeries ≤ partialProduct N :=
  ciInf_le partialProduct_bddBelow N

lemma le_singularSeries {N : ℕ} (hN : 3 ≤ N) :
    partialProduct N * (1 - 1 / ((N : ℝ) - 2)) ≤ singularSeries := by
  apply le_ciInf
  intro M
  rcases le_total N M with h | h
  · exact partialProduct_lower_bound hN h
  · have h1 : partialProduct N ≤ partialProduct M := partialProduct_antitone h
    have hN' : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : (0 : ℝ) ≤ 1 / ((N : ℝ) - 2) := div_nonneg zero_le_one (by linarith)
    nlinarith [partialProduct_nonneg N]

/-- The truncation at `6` only sees the primes `3` and `5`. -/
lemma partialProduct_six : partialProduct 6 = 45 / 64 := by
  have h0 : ¬ Nat.Prime 0 := by decide
  have h1 : ¬ Nat.Prime 1 := by decide
  have h3 : Nat.Prime 3 := by norm_num
  have h4 : ¬ Nat.Prime 4 := by decide
  have h5 : Nat.Prime 5 := by norm_num
  simp [partialProduct, Finset.prod_range_succ, localFactor, h0, h1, h3, h4, h5]
  norm_num

/-- The singular series is positive: the infinite product does not degenerate to `0`. -/
theorem singularSeries_pos : 0 < singularSeries := by
  have h := le_singularSeries (N := 6) (by norm_num)
  rw [partialProduct_six] at h
  norm_num at h
  linarith

/-! ### The main theorem -/

/-- **Effective convergence rate for the singular series.**
For every `N ≥ 3`, the truncated Hardy–Littlewood twin-prime singular series
`𝔖(N) = ∏_{p < N, p odd prime} (1 - 1/(p-1)^2)` approximates its limit `𝔖` with error at most
`1/(N-2)`. -/
theorem SingularSeriesConvergenceRate {N : ℕ} (hN : 3 ≤ N) :
    |partialProduct N - singularSeries| ≤ 1 / ((N : ℝ) - 2) := by
  have hN' : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) - 2 := by linarith
  have hupper := singularSeries_le N
  have hlower := le_singularSeries hN
  have hle1 := partialProduct_le_one N
  have hnn := partialProduct_nonneg N
  have hq : (0 : ℝ) ≤ 1 / ((N : ℝ) - 2) := div_nonneg zero_le_one (by linarith)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end Brockian

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

