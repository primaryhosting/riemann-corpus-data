import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Scope of this file.

Li's criterion states that the Riemann hypothesis holds iff the Li coefficients
`λ n = ∑_ρ (1 - (1 - 1/ρ)^n)` (the sum running over the nontrivial zeros of the Riemann zeta
function) are nonnegative for all `n ≥ 1`.  The arithmetic input -- the Hadamard factorisation of
the completed zeta function, which identifies `λ n` with a sum over the zeros -- is not available
in Mathlib.  What is formalised and proved here, unconditionally and without any extra axioms, is
the function-theoretic core of the criterion for a finite zero multiset: for a finite family of
nonzero complex numbers stable under the functional-equation symmetry `ρ ↦ 1 - ρ`, all members lie
on the critical line iff all Li coefficients of the family are nonnegative.  The hard direction is
the Bombieri--Lagarias style argument: if some `1 - 1/ρ` lies outside the closed unit disc, then a
compactness (simultaneous Dirichlet approximation) argument produces arbitrarily large exponents
`d` for which all `d`-th powers point into the right half plane, and the largest one then makes
`λ d` negative.
-/

open scoped BigOperators
open Finset Filter

namespace Frontier

/-- The `n`-th **Li coefficient** attached to a finite family of (nonzero) complex numbers
`ρ : ι → ℂ`, thought of as the zeros of a completed zeta function, listed with multiplicity:
`λ n = ∑ ρ, Re (1 - (1 - 1/ρ) ^ n)`. -/
noncomputable def liCoeff {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (n : ℕ) : ℝ :=
  ∑ i, (1 - (1 - 1 / ρ i) ^ n).re

/-- The Möbius transform `ρ ↦ 1 - 1/ρ` maps the closed half plane `Re ρ ≥ 1/2` onto the
closed unit disc. -/
lemma norm_one_sub_inv_le_one_iff {ρ : ℂ} (h : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ ≤ 1 ↔ 1 / 2 ≤ ρ.re := by
  have h1 : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h1, norm_div, div_le_one (by positivity)]
  rw [show ‖ρ - 1‖ ≤ ‖ρ‖ ↔ ‖ρ - 1‖ ^ 2 ≤ ‖ρ‖ ^ 2 from
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).symm]
  have e1 : ‖ρ - 1‖ ^ 2 = (ρ.re - 1) ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm]; simp [Complex.normSq_apply]; ring
  have e2 : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm]; simp [Complex.normSq_apply]; ring
  rw [e1, e2]
  constructor <;> intro h <;> nlinarith

/-- Easy direction: if all the numbers `1 - 1/ρ` lie in the closed unit disc, then every Li
coefficient is nonnegative. -/
lemma liCoeff_nonneg_of_norm_le_one {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (h : ∀ i, ‖1 - 1 / ρ i‖ ≤ 1) (n : ℕ) : 0 ≤ liCoeff ρ n := by
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [Complex.sub_re, Complex.one_re, sub_nonneg]
  calc ((1 - 1 / ρ i) ^ n).re ≤ ‖(1 - 1 / ρ i) ^ n‖ := Complex.re_le_norm _
    _ = ‖1 - 1 / ρ i‖ ^ n := by rw [norm_pow]
    _ ≤ 1 := pow_le_one₀ (norm_nonneg _) (h i)

/-- A simultaneous-recurrence (Dirichlet-type) statement, proved by compactness: for a finite
family of complex numbers there are arbitrarily large exponents `d` for which all the powers
`z i ^ d` point into the right half plane, with `Re (z i ^ d) ≥ ‖z i‖ ^ d / 2`. -/
lemma exists_pow_re_ge_half {ι : Type*} [Fintype ι] (z : ι → ℂ) (L : ℕ) :
    ∃ d, L ≤ d ∧ ∀ i, ‖z i‖ ^ d / 2 ≤ (z i ^ d).re := by
  classical
  set w : ι → ℂ := fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ) with hwdef
  have hw : ∀ i, ‖w i‖ = 1 := by
    intro i
    by_cases hz : z i = 0
    · simp [hwdef, hz]
    · simp [hwdef, hz, norm_ne_zero_iff.2 hz]
  have hbase : ∀ i, ((‖z i‖ : ℂ)) * w i = z i := by
    intro i
    by_cases hz : z i = 0
    · simp [hwdef, hz]
    · have h1 : (‖z i‖ : ℂ) ≠ 0 := by simpa using hz
      simp only [hwdef, hz, if_false]
      field_simp
  have hzw : ∀ (i : ι) (n : ℕ), z i ^ n = ((‖z i‖ : ℂ)) ^ n * w i ^ n := by
    intro i n; rw [← mul_pow, hbase]
  set F : ℕ → (ι → ℂ) := fun n i => w i ^ n with hFdef
  have hF : ∀ n, F n ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun i => ?_)
    rw [hFdef]
    simp [norm_pow, hw i]
  obtain ⟨a, -, φ, hφ, hconv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hF
  have hc : CauchySeq (F ∘ φ) := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  obtain ⟨N, hN⟩ := hc (1 / 2) (by norm_num)
  have hmono : ∀ k : ℕ, φ N + k ≤ φ (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h := hφ (show N + k < N + (k + 1) by omega)
        omega
  have hLd : φ N + L ≤ φ (N + L) := hmono L
  refine ⟨φ (N + L) - φ N, by omega, fun i => ?_⟩
  set d := φ (N + L) - φ N with hd
  have hsum : φ N + d = φ (N + L) := by omega
  have hdist : dist (F (φ (N + L)) i) (F (φ N) i) < 1 / 2 :=
    lt_of_le_of_lt (dist_le_pi_dist _ _ i) (hN (N + L) (by omega) N (by omega))
  have hkey : ‖w i ^ d - 1‖ < 1 / 2 := by
    have h1 : w i ^ (φ (N + L)) - w i ^ (φ N) = w i ^ (φ N) * (w i ^ d - 1) := by
      rw [mul_sub, mul_one, ← pow_add, hsum]
    have h2 : dist (F (φ (N + L)) i) (F (φ N) i) = ‖w i ^ (φ (N + L)) - w i ^ (φ N)‖ := by
      simp [hFdef, Complex.dist_eq]
    rw [h2, h1, norm_mul, norm_pow, hw i, one_pow, one_mul] at hdist
    exact hdist
  have hre : (1 : ℝ) / 2 ≤ (w i ^ d).re := by
    have h3 : (1 - w i ^ d).re ≤ ‖1 - w i ^ d‖ := Complex.re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h3
    rw [show ‖1 - w i ^ d‖ = ‖w i ^ d - 1‖ from norm_sub_rev _ _] at h3
    linarith
  calc ‖z i‖ ^ d / 2 = ‖z i‖ ^ d * (1 / 2) := by ring
    _ ≤ ‖z i‖ ^ d * (w i ^ d).re := mul_le_mul_of_nonneg_left hre (by positivity)
    _ = (z i ^ d).re := by rw [hzw i d, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/-- Hard direction: nonnegativity of all Li coefficients forces every `1 - 1/ρ` into the closed
unit disc. -/
lemma norm_le_one_of_liCoeff_nonneg {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (h : ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff ρ n) (i0 : ι) : ‖1 - 1 / ρ i0‖ ≤ 1 := by
  classical
  by_contra hc
  push_neg at hc
  set z : ι → ℂ := fun i => 1 - 1 / ρ i with hz
  set M : ℝ := ‖z i0‖ with hM
  have hM1 : 1 < M := hc
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (2 * (Fintype.card ι : ℝ) + 2) hM1
  obtain ⟨d, hdL, hd⟩ := exists_pow_re_ge_half z (max L 1)
  have hd1 : 1 ≤ d := le_trans (le_max_right L 1) hdL
  have hMd : 2 * (Fintype.card ι : ℝ) + 2 < M ^ d :=
    lt_of_lt_of_le hL (pow_le_pow_right₀ hM1.le (le_trans (le_max_left L 1) hdL))
  have hterm : ∀ i, (1 - z i ^ d).re ≤ 1 - ‖z i‖ ^ d / 2 := by
    intro i
    rw [Complex.sub_re, Complex.one_re]
    linarith [hd i]
  have hsplit : liCoeff ρ d = (1 - z i0 ^ d).re + ∑ i ∈ univ.erase i0, (1 - z i ^ d).re :=
    (Finset.add_sum_erase univ (fun i => (1 - z i ^ d).re) (mem_univ i0)).symm
  have hb1 : (1 - z i0 ^ d).re ≤ 1 - M ^ d / 2 := hterm i0
  have hb2 : ∑ i ∈ univ.erase i0, (1 - z i ^ d).re ≤ (Fintype.card ι : ℝ) := by
    calc ∑ i ∈ univ.erase i0, (1 - z i ^ d).re ≤ ∑ _i ∈ univ.erase i0, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hnn : (0 : ℝ) ≤ ‖z i‖ ^ d := by positivity
          linarith [hterm i]
      _ = ((univ.erase i0).card : ℝ) := by simp
      _ ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
  have hpos := h d hd1
  rw [hsplit] at hpos
  linarith

/-- **Li's criterion** (function-theoretic core, finite zero set).

Let `ρ : ι → ℂ` be a finite family of nonzero complex numbers -- the zeros of a completed zeta
function, listed with multiplicity -- which is stable under the functional-equation symmetry
`ρ ↦ 1 - ρ`. Then all the `ρ i` lie on the critical line `Re s = 1/2` (the Riemann hypothesis for
this zero set) if and only if all the Li coefficients
`λ n = ∑ ρ, Re (1 - (1 - 1/ρ) ^ n)` are nonnegative for `n ≥ 1`. -/
theorem RH_Li_criterion {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (h0 : ∀ i, ρ i ≠ 0) (hsymm : ∀ i, ∃ j, ρ j = 1 - ρ i) :
    (∀ i, (ρ i).re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff ρ n := by
  constructor
  · intro hre n _
    refine liCoeff_nonneg_of_norm_le_one ρ (fun i => ?_) n
    exact (norm_one_sub_inv_le_one_iff (h0 i)).2 (by rw [hre i])
  · intro hlam i
    have key : ∀ j, 1 / 2 ≤ (ρ j).re := fun j =>
      (norm_one_sub_inv_le_one_iff (h0 j)).1 (norm_le_one_of_liCoeff_nonneg ρ hlam j)
    obtain ⟨j, hj⟩ := hsymm i
    have h1 : (1 : ℝ) / 2 ≤ (1 - ρ i).re := by rw [← hj]; exact key j
    have h2 : (1 : ℝ) / 2 ≤ (ρ i).re := key i
    simp only [Complex.sub_re, Complex.one_re] at h1
    linarith

/-- Non-vacuity check: the hypotheses of `RH_Li_criterion` are satisfiable, e.g. by the
symmetric pair `1/2 ± i` on the critical line. -/
lemma RH_Li_criterion_hypotheses_satisfiable :
    ∃ ρ : Fin 2 → ℂ, (∀ i, ρ i ≠ 0) ∧ (∀ i, ∃ j, ρ j = 1 - ρ i) ∧ ∀ i, (ρ i).re = 1 / 2 := by
  refine ⟨![1 / 2 + Complex.I, 1 / 2 - Complex.I], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [Complex.ext_iff]
  · intro i
    fin_cases i
    · exact ⟨1, by simp; ring⟩
    · exact ⟨0, by simp; ring⟩
  · intro i; fin_cases i <;> simp

/-- Non-vacuity check for the other side: for the symmetric off-line pair `{1/4, 3/4}` the second
Li coefficient is negative. -/
lemma liCoeff_neg_of_offCriticalLine_example : liCoeff ![(1 / 4 : ℂ), 3 / 4] 2 < 0 := by
  simp [liCoeff, Fin.sum_univ_two]
  norm_num [Complex.ext_iff, pow_two]

end Frontier

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

