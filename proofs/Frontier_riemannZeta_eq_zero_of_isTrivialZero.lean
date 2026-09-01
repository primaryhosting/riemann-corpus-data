import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` lines to be the very first commands in a file,
so the module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the imports is rejected by the parser).
-/

open Complex

namespace Frontier

/-- `s` is a *trivial zero* of the Riemann zeta function if it is one of the points
`-2, -4, -6, …`, at which `ζ` is known to vanish (`riemannZeta_neg_two_mul_nat_add_one`). -/
def IsTrivialZero (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

/-- `s` is a *nontrivial zero* of the Riemann zeta function if `ζ s = 0` and `s` is not one of
the trivial zeros `-2, -4, -6, …`. -/
def IsNontrivialZero (s : ℂ) : Prop := riemannZeta s = 0 ∧ ¬ IsTrivialZero s

/-- **The Riemann Hypothesis**: every nontrivial zero of the Riemann zeta function lies on the
critical line `Re s = 1/2`. -/
def RH_statement : Prop := ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2

/-- Trivial zeros really are zeros of `ζ`. -/
theorem riemannZeta_eq_zero_of_isTrivialZero {s : ℂ} (hs : IsTrivialZero s) :
    riemannZeta s = 0 := by
  obtain ⟨n, rfl⟩ := hs
  exact riemannZeta_neg_two_mul_nat_add_one n

/-- Base case / known part of RH, right edge: `ζ` has no zeros in the closed half-plane
`1 ≤ Re s`. -/
theorem no_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- Base case / known part of RH, left edge: every zero of `ζ` in the closed half-plane
`Re s ≤ 0` is a trivial zero. -/
theorem isTrivialZero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) (hz : riemannZeta s = 0) :
    IsTrivialZero s := by
  -- `s = 0` is impossible, since `ζ 0 = -1/2`.
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [riemannZeta_zero] at hz; norm_num at hz
  -- Write `s = 1 - w` with `1 ≤ Re w` and apply the functional equation at `w`.
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by simp [hw, Complex.sub_re]; linarith
  have hwne : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    rw [hn] at hwre
    simp only [Complex.neg_re, Complex.natCast_re] at hwre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by
    intro h
    apply hs0
    have : s = 1 - w := by rw [hw]; ring
    rw [this, h, sub_self]
  have hsw : s = 1 - w := by rw [hw]; ring
  have key := riemannZeta_one_sub hwne hw1
  rw [← hsw, hz] at key
  -- `ζ w ≠ 0`, `Γ w ≠ 0` and `(2π)^(-w) ≠ 0`, hence `cos (π w / 2) = 0`.
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwne
  have hpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [hpi]
  have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) = 0 := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    rcases mul_eq_zero.mp key.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h₃ | h₃
          · exact absurd h₃ h2
          · exact absurd h₃ hpow
        · exact absurd h'' hGamma
      · exact h'
    · exact absurd h hzw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  -- Hence `w = 2k+1` is an odd integer with `1 ≤ Re w`, so `k ≥ 0`.
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hwk : w = 2 * (k : ℂ) + 1 := by
    field_simp at hk
    linear_combination hk
  have hkre : (0 : ℝ) ≤ (k : ℝ) := by
    have : w.re = 2 * (k : ℝ) + 1 := by rw [hwk]; simp
    rw [this] at hwre
    linarith
  have hk0 : 0 ≤ k := by exact_mod_cast hkre
  -- `s = 1 - w = -2k`, and `s ≠ 0` forces `k ≥ 1`.
  have hskey : s = -2 * (k : ℂ) := by rw [hsw, hwk]; ring
  have hkpos : 1 ≤ k := by
    rcases lt_or_ge 0 k with h | h
    · omega
    · exfalso
      have hk0' : k = 0 := le_antisymm h hk0
      apply hs0
      rw [hskey, hk0']
      simp
  refine ⟨(k - 1).toNat, ?_⟩
  have : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this
  rw [hskey, this]; ring

/-- Every nontrivial zero of `ζ` lies in the open critical strip `0 < Re s < 1`.
This is the classical "base case" of the Riemann Hypothesis. -/
theorem re_mem_critical_strip_of_isNontrivialZero {s : ℂ} (hs : IsNontrivialZero s) :
    0 < s.re ∧ s.re < 1 := by
  obtain ⟨hz, hnt⟩ := hs
  constructor
  · by_contra h
    exact hnt (isTrivialZero_of_re_nonpos (not_lt.mp h) hz)
  · by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz

/-- **Lean-checked reduction**: the Riemann Hypothesis is equivalent to the statement that all
zeros of `ζ` in the open critical strip `0 < Re s < 1` lie on the line `Re s = 1/2`. -/
theorem RH_statement_iff_critical_strip :
    RH_statement ↔ ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  constructor
  · intro h s hs0 hs1 hz
    refine h s ⟨hz, ?_⟩
    rintro ⟨n, rfl⟩
    have hre : ((-2 * ((n : ℂ) + 1)).re) = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at hs0
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h s hs
    obtain ⟨h0, h1⟩ := re_mem_critical_strip_of_isNontrivialZero hs
    exact h s h0 h1 hs.1

/-- **Lean-checked reduction**: this formalisation of the Riemann Hypothesis agrees with
Mathlib's `RiemannHypothesis`. -/
theorem RH_statement_iff_mathlib : RH_statement ↔ RiemannHypothesis := by
  constructor
  · intro h s hz hnt _
    exact h s ⟨hz, hnt⟩
  · intro h s hs
    refine h s hs.1 hs.2 ?_
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hs.1

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

