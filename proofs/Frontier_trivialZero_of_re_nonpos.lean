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
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Frontier

/-- The trivial zeros of the Riemann zeta function: the negative even integers
`-2, -4, -6, …`. -/
def IsTrivialZero (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

/-- A *nontrivial zero* of `ζ`: a zero of `ζ` which is not one of the trivial zeros. -/
def IsNontrivialZero (s : ℂ) : Prop := riemannZeta s = 0 ∧ ¬ IsTrivialZero s

/-- Every zero of `ζ` with nonpositive real part is a trivial zero.

Proof: `ζ 0 = -1/2 ≠ 0`, so `s ≠ 0`; then `w = 1 - s` has `re w ≥ 1`, and the functional
equation `ζ (1 - w) = 2 (2π)^(-w) Γ(w) cos(π w / 2) ζ(w)` together with `ζ w ≠ 0`
(zero-free region `re ≥ 1`) and `Γ w ≠ 0` forces `cos (π w / 2) = 0`, i.e. `w = 2k + 1`,
i.e. `s = -2k` with `k ≥ 1`. -/
theorem trivialZero_of_re_nonpos {s : ℂ} (hre : s.re ≤ 0) (hz : riemannZeta s = 0) :
    IsTrivialZero s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, riemannZeta_zero] at hz; norm_num at hz
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by
    simp only [hw, Complex.sub_re, Complex.one_re]; linarith
  have hwn : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n h
    have h2 : w.re = -(n : ℝ) := by rw [h]; simp
    have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
    rw [h2] at hwre; linarith
  have hw1 : w ≠ 1 := by
    intro h
    apply hs0
    have hs : s = 1 - w := by rw [hw]; ring
    rw [hs, h]; ring
  have key := riemannZeta_one_sub hwn hw1
  have h1w : (1 : ℂ) - w = s := by rw [hw]; ring
  rw [h1w, hz] at key
  have hz1 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hp : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff, hpi]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) = 0 := by
    have h0 := key.symm
    simp only [mul_eq_zero] at h0
    tauto
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hpine : ((Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp at hk
  have hsk : s = -2 * (k : ℂ) := by
    have hs : s = 1 - w := by rw [hw]; ring
    rw [hs, hk]; ring
  have hkre : s.re = -2 * (k : ℝ) := by rw [hsk]; simp
  have hk0 : 0 ≤ k := by
    rw [hkre] at hre
    have : (0 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hkne : k ≠ 0 := by
    intro h; apply hs0; rw [hsk, h]; simp
  refine ⟨(k - 1).toNat, ?_⟩
  have hcast : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by
    have h3 : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h3
  rw [hcast, hsk]; ring

/-- The trivial zeros have negative real part. -/
theorem re_neg_of_isTrivialZero {s : ℂ} (h : IsTrivialZero s) : s.re < 0 := by
  obtain ⟨n, rfl⟩ := h
  have hc : ((-2 : ℂ) * ((n : ℂ) + 1)) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [hc, Complex.ofReal_re]
  have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
  linarith

/-- The nontrivial zeros of `ζ` all lie in the open critical strip `0 < re s < 1`. -/
theorem nontrivialZero_mem_critical_strip {s : ℂ} (h : IsNontrivialZero s) :
    0 < s.re ∧ s.re < 1 := by
  obtain ⟨hz, hnt⟩ := h
  constructor
  · by_contra hcon
    exact hnt (trivialZero_of_re_nonpos (not_lt.mp hcon) hz)
  · by_contra hcon
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon) hz

/-- **Statement of the Riemann Hypothesis**, together with a Lean-checked reduction.

`RiemannHypothesis` is Mathlib's formal statement of the Riemann hypothesis: every zero `s` of
`ζ` which is not a trivial zero `-2(n+1)` (and is not the pole `s = 1`) satisfies `re s = 1/2`.

This theorem shows that this statement is *equivalent* to the a priori weaker statement that
every zero of `ζ` inside the open critical strip `0 < re s < 1` has real part `1/2`: by
`trivialZero_of_re_nonpos` and the zero-free region `re s ≥ 1`, every zero of `ζ` lying outside
the open critical strip is automatically a trivial zero, so nothing needs to be assumed there. -/
theorem RH_statement :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  constructor
  · intro h s hs0 hs1 hz
    refine h s hz (fun htriv => ?_) (fun hs => ?_)
    · exact absurd (re_neg_of_isTrivialZero htriv) (by linarith)
    · rw [hs] at hs1; simp at hs1
  · intro h s hz hnt _
    obtain ⟨h0, h1⟩ := nontrivialZero_mem_critical_strip ⟨hz, hnt⟩
    exact h s h0 h1 hz

/-- All nontrivial zeros of `ζ` lie in the open critical strip; equivalently, the Riemann
hypothesis is exactly the assertion that the zeros in that strip lie on the critical line. -/
theorem RH_iff_nontrivialZeros :
    RiemannHypothesis ↔ ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 := by
  rw [RH_statement]
  constructor
  · intro h s hs
    obtain ⟨h0, h1⟩ := nontrivialZero_mem_critical_strip hs
    exact h s h0 h1 hs.1
  · intro h s hs0 _ hz
    exact h s ⟨hz, fun htriv => absurd (re_neg_of_isTrivialZero htriv) (by linarith)⟩

end Frontier

