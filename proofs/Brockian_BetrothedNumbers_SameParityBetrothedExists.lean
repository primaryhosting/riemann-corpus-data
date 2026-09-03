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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Whether there exists a pair of *betrothed* (quasi-amicable) numbers of the same parity is an
open problem: every known betrothed pair consists of one even and one odd number.  Accordingly
this file establishes a Lean-checked **conditional reduction**: if a same-parity betrothed pair
exists, then each of its two members is either a perfect square or twice a perfect square.

The argument: for a same-parity pair, `σ m = σ n = m + n + 1` is odd; a number has an odd sum of
divisors exactly when its odd part has an odd sum of divisors, which (since all divisors of an
odd number are odd) happens exactly when its odd part has an odd number of divisors, i.e. is a
perfect square.
-/

open scoped BigOperators ArithmeticFunction.sigma Finset

namespace Brockian
namespace BetrothedNumbers

/-- `m` and `n` are a pair of *betrothed* (quasi-amicable) numbers:
they are distinct positive integers with `σ m = σ n = m + n + 1`,
i.e. the sum of the proper divisors of each is one more than the other. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- A natural number that is either a perfect square or twice a perfect square. -/
def SquareOrTwiceSquare (k : ℕ) : Prop :=
  (∃ a, k = a ^ 2) ∨ (∃ a, k = 2 * a ^ 2)

/-- The smallest betrothed pair, `(48, 75)`; note that it has opposite parity. -/
theorem betrothed_48_75 : Betrothed 48 75 :=
  ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- If every exponent in the prime factorization of `q ≠ 0` is even, then `q` is a square. -/
theorem isSquare_of_factorization_even {q : ℕ} (hq : q ≠ 0)
    (h : ∀ p, Even (q.factorization p)) : ∃ c, q = c ^ 2 := by
  refine ⟨∏ p ∈ q.primeFactors, p ^ (q.factorization p / 2), ?_⟩
  rw [← Finset.prod_pow]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hq]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_mul]
  congr 1
  obtain ⟨t, ht⟩ := h p
  omega

/-- For an odd number, the sum of its divisors is congruent mod `2` to its number of divisors,
since all of its divisors are odd. -/
theorem sigma_one_mod_two_of_odd {q : ℕ} (hq : Odd q) :
    σ 1 q % 2 = q.divisors.card % 2 := by
  rw [ArithmeticFunction.sigma_one_apply, Finset.sum_nat_mod]
  have key : ∀ d ∈ q.divisors, d % 2 = 1 := fun d hd =>
    Nat.odd_iff.mp (hq.of_dvd_nat (Nat.dvd_of_mem_divisors hd))
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul, mul_one]

/-- An odd number with an odd sum of divisors is a perfect square. -/
theorem isSquare_of_odd_of_odd_sigma {q : ℕ} (hq0 : q ≠ 0) (hq : Odd q)
    (hs : Odd (σ 1 q)) : ∃ c, q = c ^ 2 := by
  rw [Nat.odd_iff] at hs
  have hcard : q.divisors.card % 2 = 1 := by rw [← sigma_one_mod_two_of_odd hq]; exact hs
  refine isSquare_of_factorization_even hq0 fun p => ?_
  rcases Nat.even_or_odd (q.factorization p) with h | h
  · exact h
  · exfalso
    have hne : q.factorization p ≠ 0 := by rw [Nat.odd_iff] at h; omega
    have hp : p ∈ q.factorization.support := Finsupp.mem_support_iff.mpr hne
    have hdvd : (q.factorization p + 1) ∣ q.divisors.card := by
      rw [Nat.card_divisors hq0]
      exact Finset.dvd_prod_of_mem (fun a => q.factorization a + 1) hp
    have h2 : (2 : ℕ) ∣ q.divisors.card := by
      refine dvd_trans ?_ hdvd
      rw [Nat.odd_iff] at h
      omega
    omega

/-- Any positive number with an odd sum of divisors is a perfect square or twice one. -/
theorem squareOrTwiceSquare_of_odd_sigma {k : ℕ} (hk : k ≠ 0) (hs : Odd (σ 1 k)) :
    SquareOrTwiceSquare k := by
  set t := k.factorization 2 with ht
  set q := k / 2 ^ t with hqdef
  have hsplit : 2 ^ t * q = k := Nat.ordProj_mul_ordCompl_eq_self k 2
  have hq0 : q ≠ 0 := (Nat.ordCompl_pos 2 hk).ne'
  have hqodd : Odd q :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hk))
  have hcop : Nat.Coprime (2 ^ t) q := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hqodd)
  have hmul : σ 1 k = σ 1 (2 ^ t) * σ 1 q := by
    rw [← hsplit]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hsq : Odd (σ 1 q) := by
    rw [hmul] at hs
    exact (Nat.odd_mul.mp hs).2
  obtain ⟨c, hc⟩ := isSquare_of_odd_of_odd_sigma hq0 hqodd hsq
  rcases Nat.even_or_odd t with he | ho
  · obtain ⟨s, hsv⟩ := he
    exact Or.inl ⟨2 ^ s * c, by rw [← hsplit, hc, hsv]; ring⟩
  · obtain ⟨s, hsv⟩ := ho
    exact Or.inr ⟨2 ^ s * c, by rw [← hsplit, hc, hsv]; ring⟩

/-- **Same-parity betrothed pairs.**  Whether a betrothed pair of equal parity exists is an
open problem (all known betrothed pairs have opposite parity).  What is proved here is a
Lean-checked structural reduction: *if* a same-parity betrothed pair exists, then there is one
(indeed, the very same pair) whose two members are each either a perfect square or twice a
perfect square. -/
theorem SameParityBetrothedExists
    (h : ∃ m n, Betrothed m n ∧ m % 2 = n % 2) :
    ∃ m n, Betrothed m n ∧ m % 2 = n % 2 ∧
      SquareOrTwiceSquare m ∧ SquareOrTwiceSquare n := by
  obtain ⟨m, n, ⟨hm, hn, hmn, hsm, hsn⟩, hpar⟩ := h
  have hodd : Odd (m + n + 1) := Nat.odd_iff.mpr (by omega)
  refine ⟨m, n, ⟨hm, hn, hmn, hsm, hsn⟩, hpar, ?_, ?_⟩
  · exact squareOrTwiceSquare_of_odd_sigma hm.ne' (hsm ▸ hodd)
  · exact squareOrTwiceSquare_of_odd_sigma hn.ne' (hsn ▸ hodd)

end BetrothedNumbers
end Brockian

