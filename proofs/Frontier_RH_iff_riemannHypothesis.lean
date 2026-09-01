import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open Complex

/-- A *trivial zero* of the Riemann zeta function is one of the points `-2, -4, -6, …`. -/
def IsTrivialZero (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

/-- A *nontrivial zero* of the Riemann zeta function: a zero which is neither a trivial zero
nor the pole `s = 1` (at which Mathlib's `riemannZeta` takes a junk value). -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ¬ IsTrivialZero s ∧ s ≠ 1

/-- The Riemann Hypothesis: every nontrivial zero of `ζ` has real part `1/2`.
This is equivalent to Mathlib's `RiemannHypothesis`, see `RH_iff_riemannHypothesis`. -/
def RH : Prop := ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2

theorem RH_iff_riemannHypothesis : RH ↔ RiemannHypothesis := by
  constructor
  · intro h s hs h1 h2
    exact h s ⟨hs, h1, h2⟩
  · intro h s hs
    exact h s hs.1 hs.2.1 hs.2.2

/-- The functional equation in the multiplicative form used below: if `Re w > 0` and `w ≠ 1`
(so that in particular `w` is not a nonpositive integer), then
`ζ (1 - w) = 2 * (2π)^(-w) * Γ w * cos (π w / 2) * ζ w`. -/
theorem zeta_one_sub_of_re_pos {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    riemannZeta (1 - w) =
      2 * (2 * (π : ℂ)) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w := by
  refine riemannZeta_one_sub (fun n => ?_) hw1
  intro hcon
  rw [hcon] at hw
  simp at hw
  linarith [hw, Nat.cast_nonneg (α := ℝ) n]

/-- Zeros of `ζ` in the closed half plane `Re s ≥ 1` do not exist. -/
theorem zeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- `ζ` does not vanish at `0`. -/
theorem zeta_zero_ne_zero : riemannZeta 0 ≠ 0 := by
  rw [riemannZeta_zero]
  norm_num

/-- Every zero of `ζ` in the closed half plane `Re s ≤ 0` is a trivial zero. -/
theorem isTrivialZero_of_re_nonpos {s : ℂ} (hz : riemannZeta s = 0) (hs : s.re ≤ 0) :
    IsTrivialZero s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact zeta_zero_ne_zero hz
  have hwre : 1 ≤ ((1 : ℂ) - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hw1 : (1 : ℂ) - s ≠ 1 := by
    intro h
    exact hs0 (by linear_combination -h)
  have heq := zeta_one_sub_of_re_pos (by linarith) hw1
  rw [show (1 : ℂ) - (1 - s) = s by ring, hz] at heq
  have hzw : riemannZeta (1 - s) ≠ 0 := zeta_ne_zero_of_one_le_re hwre
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpi : ((π : ℂ)) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hp : (2 * (π : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro h
    exact (mul_ne_zero two_ne_zero hpi) h.1
  have hcos : Complex.cos (π * (1 - s) / 2) = 0 := by
    rcases mul_eq_zero.mp heq.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h₃ | h₃
          · exact absurd h₃ two_ne_zero
          · exact absurd h₃ hp
        · exact absurd h'' hG
      · exact h'
    · exact absurd h hzw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hsk : s = -2 * (k : ℂ) := by
    field_simp at hk
    linear_combination -hk
  have hkre : ((k : ℝ)) ≥ 0 := by
    have : s.re = -2 * (k : ℝ) := by
      rw [hsk]; simp
    rw [this] at hs
    linarith
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hsk
    exact hs0 hsk
  have hk1 : 1 ≤ k := by
    have : (0 : ℤ) ≤ k := by exact_mod_cast hkre
    omega
  refine ⟨(k - 1).toNat, ?_⟩
  have : ((((k - 1).toNat : ℕ) : ℂ)) = (k : ℂ) - 1 := by
    have : (((k - 1).toNat : ℤ)) = k - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) this
  rw [hsk, this]
  ring

/-- **Left edge of the critical strip.** Every nontrivial zero has positive real part. -/
theorem re_pos_of_isNontrivialZero {s : ℂ} (hs : IsNontrivialZero s) : 0 < s.re := by
  by_contra h
  exact hs.2.1 (isTrivialZero_of_re_nonpos hs.1 (le_of_not_gt h))

/-- **Right edge of the critical strip.** Every nontrivial zero has real part `< 1`. -/
theorem re_lt_one_of_isNontrivialZero {s : ℂ} (hs : IsNontrivialZero s) : s.re < 1 := by
  by_contra h
  exact zeta_ne_zero_of_one_le_re (le_of_not_gt h) hs.1

/-- **The critical strip.** Every nontrivial zero of `ζ` lies in the open strip `0 < Re s < 1`. -/
theorem isNontrivialZero_mem_critical_strip {s : ℂ} (hs : IsNontrivialZero s) :
    0 < s.re ∧ s.re < 1 :=
  ⟨re_pos_of_isNontrivialZero hs, re_lt_one_of_isNontrivialZero hs⟩

/-- The real part of a trivial zero is at most `-2`. -/
theorem re_le_neg_two_of_isTrivialZero {s : ℂ} (hs : IsTrivialZero s) : s.re ≤ -2 := by
  obtain ⟨n, rfl⟩ := hs
  have : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [this]
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- **Reflection.** If `s` is a nontrivial zero, so is `1 - s`. -/
theorem isNontrivialZero_one_sub {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero (1 - s) := by
  obtain ⟨hre0, hre1⟩ := isNontrivialZero_mem_critical_strip hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hre0
  have hs1 : s ≠ 1 := hs.2.2
  have hzero : riemannZeta (1 - s) = 0 := by
    rw [zeta_one_sub_of_re_pos hre0 hs1, hs.1, mul_zero]
  refine ⟨hzero, ?_, ?_⟩
  · intro ht
    have := re_le_neg_two_of_isTrivialZero ht
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  · intro h
    exact hs0 (by linear_combination -h)

/-- **Main statement (Lean-checked reduction).**
The Riemann Hypothesis — *every nontrivial zero of `ζ` has real part `1/2`* — is equivalent to
the a priori weaker assertion that `ζ` has no zero at all strictly to the right of the critical
line `Re s = 1/2`.  The reduction uses the functional equation together with the classical
zero-free half plane `Re s ≥ 1`. -/
theorem RH_statement :
    RiemannHypothesis ↔ ∀ s : ℂ, riemannZeta s = 0 → s.re ≤ 1 / 2 := by
  rw [← RH_iff_riemannHypothesis]
  constructor
  · intro h s hz
    by_cases ht : IsTrivialZero s
    · have := re_le_neg_two_of_isTrivialZero ht
      linarith
    · by_cases h1 : s = 1
      · subst h1
        exact absurd hz (zeta_ne_zero_of_one_le_re (by simp))
      · exact le_of_eq (h s ⟨hz, ht, h1⟩)
  · intro h s hs
    have h1 := h s hs.1
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have h2 := h _ (isNontrivialZero_one_sub hs).1
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith

end Frontier

