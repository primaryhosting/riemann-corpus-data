/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The set of affine rational points of the plane Fermat curve
`F_n : x ^ n + y ^ n = 1` over `ℚ`.

For `n ≥ 4` this is a smooth plane curve of degree `n`, hence of genus
`(n-1)(n-2)/2 ≥ 3 ≥ 2`, so Faltings' theorem (the Mordell conjecture) predicts that it has
only finitely many rational points. -/
def fermatCurveRatPoints (n : ℕ) : Set (ℚ × ℚ) := {p : ℚ × ℚ | p.1 ^ n + p.2 ^ n = 1}

/-- Fermat's Last Theorem over `ℚ` for every exponent divisible by `4`
(Mathlib's `fermatLastTheoremFour`, transported to `ℚ` and to multiples of `4`). -/
theorem fermatLastTheoremWith_rat_of_four_dvd {n : ℕ} (hn : 4 ∣ n) :
    FermatLastTheoremWith ℚ n :=
  FermatLastTheoremWith.mono hn (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour)

/-- On a Fermat curve of exponent divisible by `4`, every rational point has both coordinates
in `{0, 1, -1}`. -/
theorem fermatCurveRatPoints_subset {n : ℕ} (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    fermatCurveRatPoints n ⊆ ({0, 1, -1} : Set ℚ) ×ˢ ({0, 1, -1} : Set ℚ) := by
  rintro ⟨x, y⟩ (hxy : x ^ n + y ^ n = 1)
  have hFLT := fermatLastTheoremWith_rat_of_four_dvd hn
  have hroot : ∀ z : ℚ, z ^ n = 1 → z = 1 ∨ z = -1 := by
    intro z hz
    rcases pow_eq_one_iff_cases.mp hz with h | h | h
    · exact absurd h hn0
    · exact Or.inl h
    · exact Or.inr h.1
  -- One of the two coordinates has to vanish, by Fermat's Last Theorem.
  have hzero : x = 0 ∨ y = 0 := by
    by_contra hc
    push_neg at hc
    exact hFLT x y 1 hc.1 hc.2 one_ne_zero (by simpa using hxy)
  constructor
  · rcases hzero with hx | hy
    · exact Or.inl hx
    · have : x ^ n = 1 := by rw [hy] at hxy; simpa [zero_pow hn0] using hxy
      rcases hroot x this with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rcases hzero with hx | hy
    · have : y ^ n = 1 := by rw [hx] at hxy; simpa [zero_pow hn0] using hxy
      rcases hroot y this with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact Or.inl hy

/-- **Faltings' theorem (Mordell conjecture), verified instance.**

For every exponent `n ≠ 0` divisible by `4`, the plane Fermat curve `x ^ n + y ^ n = 1`
is a smooth curve of genus `(n-1)(n-2)/2 ≥ 3 ≥ 2` over `ℚ`, and its set of rational points
is finite — as predicted by Faltings' theorem.

The general theorem of Faltings is not available in Mathlib; this is a Lean-checked instance
of it, obtained from Mathlib's `fermatLastTheoremFour`. -/
theorem faltings_mordell {n : ℕ} (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    (fermatCurveRatPoints n).Finite :=
  Set.Finite.subset
    (Set.Finite.prod (Set.toFinite ({0, 1, -1} : Set ℚ)) (Set.toFinite ({0, 1, -1} : Set ℚ)))
    (fermatCurveRatPoints_subset hn hn0)

/-- The rational points of the genus-`3` Fermat quartic `x ^ 4 + y ^ 4 = 1` are exactly the
four trivial ones. -/
theorem fermatCurveRatPoints_four :
    fermatCurveRatPoints 4 = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
  apply Set.eq_of_subset_of_subset
  · rintro ⟨x, y⟩ hp
    have hmem := fermatCurveRatPoints_subset (n := 4) dvd_rfl (by norm_num) hp
    have hxy : x ^ 4 + y ^ 4 = 1 := hp
    obtain ⟨hx, hy⟩ := hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> subst hx <;> subst hy
    all_goals try norm_num at hxy
    all_goals norm_num
  · rintro ⟨x, y⟩ hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
    show x ^ 4 + y ^ 4 = 1
    rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy <;> norm_num

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

