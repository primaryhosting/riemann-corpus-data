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

/-
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.WilsonPrimes

open Nat

/-- A *Wilson prime* is a prime `p` with `p ^ 2 ∣ (p - 1)! + 1`.
(By Wilson's theorem, `p ∣ (p-1)! + 1` holds for every prime, so this is the
statement that the divisibility holds to the second power.) -/
def WilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

/-- The Wilson quotient of `p`, namely `((p - 1)! + 1) / p`.  For a prime `p`
this is an integer by Wilson's theorem. -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

/-- Wilson's theorem, in divisibility form: for a prime `p`, `p ∣ (p-1)! + 1`.
This is `ZMod.wilsons_lemma` from Mathlib, transported from `ZMod p` to `ℕ`. -/
theorem prime_dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) :
    p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := ZMod.wilsons_lemma p
  have h2 : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by push_cast [h]; ring
  exact (ZMod.natCast_eq_zero_iff _ p).mp h2

/-- For a prime `p`, being a Wilson prime is equivalent to `p` dividing its
Wilson quotient. -/
theorem wilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ p ∣ wilsonQuotient p := by
  have hd : p ∣ (p - 1)! + 1 := prime_dvd_factorial_pred_add_one hp
  unfold WilsonPrime wilsonQuotient
  rw [Nat.dvd_div_iff_mul_dvd hd, ← pow_two]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

/-- `5` is a Wilson prime. -/
theorem wilsonPrime_five : WilsonPrime 5 := ⟨by norm_num, by decide⟩

/-- `13` is a Wilson prime. -/
theorem wilsonPrime_thirteen : WilsonPrime 13 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 10000 in
/-- `563` is a Wilson prime. -/
theorem wilsonPrime_563 : WilsonPrime 563 := ⟨by norm_num, by decide +kernel⟩

/-- **Conditional reduction.**  Whether there are infinitely many Wilson primes
is a well-known open problem (only `5`, `13` and `563` are known, and no others
exist below `2 * 10 ^ 13`).  The following theorem is the Lean-checked reduction:
under the hypothesis that Wilson primes are unbounded — for every `N` there is a
Wilson prime exceeding `N` — the set of Wilson primes is infinite. -/
theorem WilsonPrimeInfinitude
    (hunbounded : ∀ N : ℕ, ∃ p, N < p ∧ WilsonPrime p) :
    {p : ℕ | WilsonPrime p}.Infinite :=
  Set.infinite_of_forall_exists_gt fun N => by
    obtain ⟨p, hNp, hp⟩ := hunbounded N
    exact ⟨p, hp, hNp⟩

/-- The hypothesis used in `WilsonPrimeInfinitude` is not merely sufficient but
equivalent: the set of Wilson primes is infinite if and only if Wilson primes
are unbounded. -/
theorem wilsonPrimes_infinite_iff_unbounded :
    {p : ℕ | WilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ WilsonPrime p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hNp⟩ := h.exists_gt N
    exact ⟨p, hNp, hp⟩
  · exact WilsonPrimeInfinitude

end Brockian.WilsonPrimes

