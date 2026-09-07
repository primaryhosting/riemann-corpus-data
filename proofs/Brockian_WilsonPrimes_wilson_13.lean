/-
  Brockian/WilsonPrimes.lean — Wilson primes, Wilson's-theorem grounding, and the
  OPEN infinitude question.

  Wilson's theorem: if `p` is prime then `p ∣ (p−1)! + 1`. A **Wilson prime**
  strengthens the divisibility to the square: `p² ∣ (p−1)! + 1`. Only THREE Wilson
  primes are known — 5, 13, 563 — and it is an OPEN problem whether there are
  infinitely many (indeed whether any exist beyond 563). Here we:

    (1) verify the two computationally small Wilson primes 5 and 13
        (563 is out of reach: 562! is astronomically large);
    (2) ground the base p-divisibility in Mathlib's Wilson lemma
        (`ZMod.wilsons_lemma`), the proven weaker fact Wilson primes strengthen;
    (3) exhibit a prime (7) that is NOT a Wilson prime, showing Wilson primes are
        strictly rarer than primes.

  The infinitude statement `WilsonPrimeInfinitude` is recorded as an UNPROVEN `def`
  (an open conjecture). It is NEVER asserted or proven — doing so is unknown to
  mathematics.

  Verification (spec §2A triple verification):
    - local `lake build` : deferred to REMOTE AXLE (authoritative)
    - `#print axioms`     : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent    : verified @ lean-4.32.0
-/
import Mathlib

open scoped Nat

namespace Brockian.WilsonPrimes

/-- `p` is a **Wilson prime**: `p` is prime and `p²` divides `(p−1)! + 1`
(strictly stronger than Wilson's theorem, which gives only `p ∣ (p−1)! + 1`). -/
def WilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (Nat.factorial (p - 1) + 1)

/-- **OPEN CONJECTURE — recorded, never asserted.** There are infinitely many Wilson
primes. Only 5, 13, 563 are known; whether infinitely many exist is unresolved. This
is an unproven `def`; no theorem in this file proves or assumes it. -/
def WilsonPrimeInfinitude : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ WilsonPrime p

/-! ## (1) The two computationally small Wilson primes -/

/-- **FLAGSHIP.** `5` is a Wilson prime: `5² = 25` divides `4! + 1 = 25`. -/
theorem wilson_5 : WilsonPrime 5 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [Nat.factorial]

/-- **FLAGSHIP.** `13` is a Wilson prime: `13² = 169` divides
`12! + 1 = 479001601 = 169 · 2834329`. -/
theorem wilson_13 : WilsonPrime 13 := by
  refine ⟨by norm_num, ?_⟩
  have h12 : Nat.factorial 12 = 479001600 := by norm_num [Nat.factorial]
  rw [show (13 : ℕ) - 1 = 12 from rfl, h12]
  norm_num

/-! ## (2) Grounding: Wilson's theorem gives the base p-divisibility -/

/-- **Wilson's-theorem grounding.** For every prime `p`, `p ∣ (p−1)! + 1`. This is the
proven weaker fact that a Wilson prime strengthens from `p` to `p²`. Derived from
Mathlib's `ZMod.wilsons_lemma : ((p−1)! : ZMod p) = -1`. -/
theorem prime_dvd_factorial_add_one {p : ℕ} (hp : p.Prime) :
    p ∣ (Nat.factorial (p - 1) + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, ZMod.wilsons_lemma]
  ring

/-! ## (3) A prime that is not a Wilson prime -/

/-- `7` is prime and (by Wilson's theorem) `7 ∣ 6! + 1 = 721`, but `7² = 49 ∤ 721`
(since `721 = 7 · 103`), so `7` is NOT a Wilson prime. Wilson primes are strictly
rarer than primes. -/
theorem seven_not_wilson : ¬ WilsonPrime 7 := by
  rintro ⟨-, hdvd⟩
  revert hdvd
  norm_num [Nat.factorial]

end Brockian.WilsonPrimes
