import Mathlib

/-!
# Harmonic Divisor Numbers (Ore numbers)

A natural number `n` is a *harmonic divisor number* (Ore number) when the
harmonic mean of its positive divisors is an integer.  The harmonic mean of the
divisors of `n` equals `n · d(n) / σ(n)`, so `n` is harmonic exactly when
`σ(n) ∣ n · d(n)` and the quotient is the (integer) harmonic mean.

Here `d(n)` is the number of divisors and `σ(n)` the sum of divisors.
Every perfect number is harmonic.  The first Ore numbers are
`1, 6, 28, 140, 270, 496, …`.

All facts below are settled by `decide` on concrete divisor computations.
-/

namespace Brockian.HarmonicDivisor

/-- `σ(n)` : the sum of the positive divisors of `n`. -/
def sig (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `d(n)` : the number of positive divisors of `n`. -/
def numDiv (n : ℕ) : ℕ := n.divisors.card

/-- `n` is a harmonic divisor number: `σ(n)` divides `n · d(n)`. -/
def isHarmonic (n : ℕ) : Prop := sig n ∣ n * numDiv n

-- Harmonic witnesses: 6, 28, 140, 270 are Ore numbers.
theorem harmonic_6   : isHarmonic 6   := by unfold isHarmonic; decide
theorem harmonic_28  : isHarmonic 28  := by unfold isHarmonic; decide
theorem harmonic_140 : isHarmonic 140 := by unfold isHarmonic; decide
theorem harmonic_270 : isHarmonic 270 := by unfold isHarmonic; decide

-- The integer harmonic means: 6→2, 28→3, 140→5, 270→6.
theorem harmonic_mean_6   : 6   * numDiv 6   / sig 6   = 2 := by decide
theorem harmonic_mean_28  : 28  * numDiv 28  / sig 28  = 3 := by decide
theorem harmonic_mean_140 : 140 * numDiv 140 / sig 140 = 5 := by decide
theorem harmonic_mean_270 : 270 * numDiv 270 / sig 270 = 6 := by decide

-- Honesty: 4 is not harmonic. d(4)=3, σ(4)=7, 4·3=12, and 7 ∤ 12.
theorem not_harmonic_4 : ¬ isHarmonic 4 := by unfold isHarmonic; decide

/-- The four displayed Ore numbers, bundled. -/
theorem harmonic_examples :
    isHarmonic 6 ∧ isHarmonic 28 ∧ isHarmonic 140 ∧ isHarmonic 270 :=
  ⟨harmonic_6, harmonic_28, harmonic_140, harmonic_270⟩

end Brockian.HarmonicDivisor
