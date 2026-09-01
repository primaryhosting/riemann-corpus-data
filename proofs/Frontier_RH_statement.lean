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

/-- If `s` is a zero of `ζ` which is neither `0` nor a trivial zero `-2(n+1)`, then `1 - s` is
also a zero of `ζ`.  This is the functional equation, in the form we need it: the completed zeta
function `Λ` vanishes at `s`, and `Λ (1 - s) = Λ s`. -/
theorem riemannZeta_one_sub_eq_zero {s : ℂ} (h0 : riemannZeta s = 0) (hs0 : s ≠ 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : riemannZeta (1 - s) = 0 := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero h0
  have hΓ : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, rfl⟩
    match n with
    | 0 => exact hs0 (by norm_num)
    | (n + 1) => exact htriv ⟨n, by push_cast; ring⟩
  have hΛ : completedRiemannZeta s = 0 := by
    have := riemannZeta_def_of_ne_zero hs0
    rw [h0, eq_comm, div_eq_zero_iff] at this
    exact this.resolve_right hΓ
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hΛ, zero_div]

/-- **The Riemann Hypothesis**, as stated in Mathlib (`RiemannHypothesis`: every zero of `ζ`
other than the trivial zeros `-2(n+1)` and the pole `s = 1` lies on the line `Re s = 1/2`), is
equivalent to the *a priori* weaker statement that `ζ` has no zero in the open right half
`1/2 < Re s < 1` of the critical strip.

This is a Lean-checked reduction of RH: it eliminates, unconditionally, all the zeros outside
that region.  Zeros with `Re s ≥ 1` are ruled out by the nonvanishing theorem
`riemannZeta_ne_zero_of_one_le_re`, and zeros with `Re s < 1/2` are transported to zeros with
`Re s > 1/2` by the functional equation. -/
theorem RH_statement :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  constructor
  · intro h s hlt hlt' hz
    have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      simp only [neg_mul, Complex.neg_re, Complex.mul_re] at hlt
      norm_num at hlt
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hs1 : s ≠ 1 := by
      rintro rfl
      simp at hlt'
    exact absurd (h s hz htriv hs1) (by linarith)
  · intro h s hz htriv hs1
    -- No zeros at all strictly to the right of the critical line.
    have key : ∀ t : ℂ, riemannZeta t = 0 → ¬ (1 / 2 < t.re) := by
      intro t ht hgt
      rcases lt_or_ge t.re 1 with hlt | hge
      · exact h t hgt hlt ht
      · exact riemannZeta_ne_zero_of_one_le_re hge ht
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hz
      norm_num at hz
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · -- reflect across the critical line
      have h1s := riemannZeta_one_sub_eq_zero hz hs0 htriv
      have : ((1 : ℂ) - s).re = 1 - s.re := by simp
      exact absurd (this ▸ (by linarith : (1 : ℝ) / 2 < 1 - s.re)) (key _ h1s)
    · exact heq
    · exact absurd hgt (key s hz)

end Frontier

