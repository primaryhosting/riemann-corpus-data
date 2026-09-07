/-
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace BetrothedNumbers

/-- The *betrothed* (quasi-amicable) partner map: `partner n = σ₁(n) - n - 1`, i.e. the sum of
the nontrivial divisors of `n` (all divisors except `1` and `n`).  Subtraction is truncated
natural subtraction, so `partner 1 = 0`. -/
def partner (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n - n - 1

/-- `m` and `n` form a **betrothed pair** (quasi-amicable pair) when they are distinct positive
integers each of whose divisor sums equals `m + n + 1`; equivalently, the sum of the nontrivial
divisors of each is the other one. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧
    ArithmeticFunction.sigma 1 m = m + n + 1 ∧ ArithmeticFunction.sigma 1 n = m + n + 1

namespace Dynamics

/-- **Characterization of betrothed pairs as nontrivial positive 2-cycles of `partner`.**

A pair `(m, n)` is a betrothed pair exactly when `m` and `n` are positive, `partner` swaps them
(`partner m = n`, `partner n = m`), and the cycle is nontrivial (`partner m ≠ m`, i.e. `m` is not
a quasi-perfect fixed point). -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔
      0 < m ∧ 0 < n ∧ partner m = n ∧ partner n = m ∧ partner m ≠ m := by
  unfold IsBetrothedPair partner
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, by omega, by omega, by omega⟩
  · rintro ⟨hm, hn, h1, h2, h3⟩
    exact ⟨hm, hn, by omega, by omega, by omega⟩

end Dynamics

/-- Sanity check: `(48, 75)` is the smallest betrothed pair. -/
example : IsBetrothedPair 48 75 := by
  exact ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

end BetrothedNumbers
end Brockian

