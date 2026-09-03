/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

/-- The (von Neumann / Shannon) entanglement entropy of a cut, computed from the
Schmidt spectrum `p` supported on the finite index set `s`. -/
noncomputable def entropy {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ i ∈ s, Real.negMulLog (p i)

/-- Pointwise form of the log-sum inequality:
`-p·log p - p·log n ≤ 1/n - p` for `0 ≤ p` and `0 < n`. -/
lemma negMulLog_sub_mul_log_le {p : ℝ} {n : ℝ} (hp : 0 ≤ p) (hn : 0 < n) :
    Real.negMulLog p - p * Real.log n ≤ 1 / n - p := by
  rcases eq_or_lt_of_le hp with h | hp'
  · -- `p = 0`: the left-hand side vanishes.
    simp [← h, Real.negMulLog, hn.le]
  · -- `p > 0`: use `log x ≥ 1 - 1/x` with `x = p * n`.
    have hx : 0 < p * n := mul_pos hp' hn
    have hlog : Real.log (1 / (p * n)) ≤ 1 / (p * n) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [one_div, Real.log_inv] at hlog
    have hlog' : 1 - (p * n)⁻¹ ≤ Real.log (p * n) := by linarith
    have hmul : p * (1 - (p * n)⁻¹) ≤ p * Real.log (p * n) :=
      mul_le_mul_of_nonneg_left hlog' hp
    have hsplit : Real.log (p * n) = Real.log p + Real.log n :=
      Real.log_mul (ne_of_gt hp') (ne_of_gt hn)
    have hpn : p * (p * n)⁻¹ = 1 / n := by
      field_simp
    rw [hsplit, mul_add] at hmul
    rw [Real.negMulLog]
    nlinarith [hmul, hpn]

/-- **Maximal-entropy bound.** A probability distribution supported on a finite set `s`
has entropy at most `log |s|`. -/
theorem entropy_le_log_card {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    entropy s p ≤ Real.log s.card := by
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h] at hsum; simp at hsum
    · exact h
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have key : ∀ i ∈ s, Real.negMulLog (p i) - p i * Real.log s.card
      ≤ 1 / (s.card : ℝ) - p i := fun i hi =>
    negMulLog_sub_mul_log_le (hnn i hi) hcard
  have hsum' : ∑ i ∈ s, (Real.negMulLog (p i) - p i * Real.log s.card)
      ≤ ∑ i ∈ s, (1 / (s.card : ℝ) - p i) := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum] at hsum'
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum'
  rw [mul_one_div, div_self (ne_of_gt hcard)] at hsum'
  simpa [entropy] using hsum'

/--
**Entanglement-entropy area law in one dimension (Hastings).**

A gapped 1D ground state admits, across every cut, a Schmidt decomposition of
bounded rank: this is the content of the matrix-product-state approximation for
gapped chains, and it is encoded here as the hypothesis `hbond`, which supplies a
bond dimension `D` bounding the number of Schmidt coefficients across the cut at
each region size `L`, uniformly in `L`.

The conclusion is the area law proper: the entanglement entropy across the cut is
bounded by a constant `C` (namely `log D`) **independent of the region size `L`**,
rather than growing with the volume of the region.

Here `spectrum L` is the Schmidt spectrum across the cut at region size `L`,
supported on the finite index set `cut L`; `hnn` and `hnorm` say it is a
probability distribution.
-/
theorem area_law_1d {ι : Type*} (cut : ℕ → Finset ι) (spectrum : ℕ → ι → ℝ)
    (hnn : ∀ L, ∀ i ∈ cut L, 0 ≤ spectrum L i)
    (hnorm : ∀ L, ∑ i ∈ cut L, spectrum L i = 1)
    (hbond : ∃ D : ℕ, ∀ L, (cut L).card ≤ D) :
    ∃ C : ℝ, ∀ L, entropy (cut L) (spectrum L) ≤ C := by
  obtain ⟨D, hD⟩ := hbond
  refine ⟨Real.log D, fun L => ?_⟩
  refine (entropy_le_log_card (cut L) (spectrum L) (hnn L) (hnorm L)).trans ?_
  have hpos : (0 : ℝ) < ((cut L).card : ℝ) := by
    have hne : (cut L).Nonempty := by
      rcases (cut L).eq_empty_or_nonempty with h | h
      · have := hnorm L; rw [h] at this; simp at this
      · exact h
    exact_mod_cast Finset.card_pos.mpr hne
  exact Real.log_le_log hpos (by exact_mod_cast hD L)

end Phys

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

