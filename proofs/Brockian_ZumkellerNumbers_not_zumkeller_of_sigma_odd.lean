import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is Zumkeller if its divisors can be split so that one part sums to half
the total divisor sum. -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- If the sum of divisors of `n` is odd, then `n` is not Zumkeller. -/
theorem not_zumkeller_of_sigma_odd (n : ℕ) (h : Odd (∑ d ∈ n.divisors, d)) : ¬ Zumkeller n := by
  rintro ⟨S, -, hS⟩
  rw [← hS] at h
  exact (Nat.not_odd_iff_even.mpr ⟨∑ d ∈ S, d, by ring⟩) h

end Brockian.ZumkellerNumbers

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

