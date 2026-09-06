import Mathlib
/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
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

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-! ## Betrothed (quasi-amicable) pairs -/

/-- `sigmaOne n = σ₁ n = ∑_{d ∣ n} d`. -/
def sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

@[simp] lemma sigmaOne_apply (n : ℕ) : sigmaOne n = ∑ d ∈ n.divisors, d := by
  rw [sigmaOne, ArithmeticFunction.sigma_one_apply]

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose
sum of divisors equals `m + n + 1`; equivalently, the sum of the divisors of each,
excluding the number itself and `1`, equals the other member. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- Sanity check that the definition is non-vacuous: `(48, 75)` is the smallest
betrothed pair (`σ₁ 48 = σ₁ 75 = 124 = 48 + 75 + 1`).  Note that its members have
opposite parity and are not coprime, as is the case for every known betrothed pair. -/
lemma isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;>
    · simp only [sigmaOne, ArithmeticFunction.sigma_one_apply]
      decide

/-! ## The rational abundancy bound

For every `N ≠ 0` one has `σ₁(N) ≤ N * ∏_{p ∣ N} p/(p-1)`, the product being over
the distinct prime factors of `N`. -/

/-- `ratio p = p / (p - 1)`, the local abundancy factor at the prime `p`. -/
def ratio (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

lemma one_le_ratio {p : ℕ} (hp : 2 ≤ p) : 1 ≤ ratio p := by
  have h : (2 : ℚ) ≤ p := by exact_mod_cast hp
  rw [ratio, le_div_iff₀ (by linarith)]
  linarith

lemma ratio_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ ratio p :=
  le_trans zero_le_one (one_le_ratio hp)

/-- `p ↦ p/(p-1)` is antitone on integers `≥ 2`. -/
lemma ratio_antitone {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) : ratio q ≤ ratio p := by
  have h1 : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have h2 : (p : ℚ) ≤ q := by exact_mod_cast hpq
  rw [ratio, ratio, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Local abundancy bound at a prime power: `σ₁(p^a) ≤ p^a * p/(p-1)`. -/
lemma sigma_prime_pow_le {p a : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.sigma 1) (p ^ a) : ℚ) ≤ (p : ℚ) ^ a * ratio p := by
  have h2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hs : ((ArithmeticFunction.sigma 1) (p ^ a) : ℚ) * ((p : ℚ) - 1) = (p : ℚ) ^ (a + 1) - 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    push_cast
    rw [geom_sum_eq (by linarith)]
    field_simp
  have he : (p : ℚ) ^ a * ratio p = (p : ℚ) ^ (a + 1) / ((p : ℚ) - 1) := by
    rw [ratio]; field_simp; ring
  rw [he, le_div_iff₀ hpos]
  linarith

/-- **The rational abundancy bound**: `σ₁(N) ≤ N * ∏_{p ∣ N} p/(p-1)`. -/
lemma sigmaOne_le_mul_prod_ratio {N : ℕ} (hN : N ≠ 0) :
    (sigmaOne N : ℚ) ≤ N * ∏ p ∈ N.primeFactors, ratio p := by
  have h1 : (ArithmeticFunction.sigma 1) N
      = ∏ p ∈ N.primeFactors, (ArithmeticFunction.sigma 1) (p ^ N.factorization p) := by
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
      ArithmeticFunction.isMultiplicative_sigma hN]
    simp [Finsupp.prod, Nat.support_factorization]
  have h2 : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    simp [Finsupp.prod, Nat.support_factorization]
  calc (sigmaOne N : ℚ)
      = ∏ p ∈ N.primeFactors, ((ArithmeticFunction.sigma 1) (p ^ N.factorization p) : ℚ) := by
        rw [sigmaOne, h1]; push_cast; ring
    _ ≤ ∏ p ∈ N.primeFactors, ((p : ℚ) ^ (N.factorization p) * ratio p) := by
        refine Finset.prod_le_prod (fun i _ => by positivity) (fun i hi => ?_)
        exact sigma_prime_pow_le (Nat.prime_of_mem_primeFactors hi)
    _ = (∏ p ∈ N.primeFactors, (p : ℚ) ^ (N.factorization p)) * ∏ p ∈ N.primeFactors, ratio p :=
        Finset.prod_mul_distrib
    _ = (N : ℚ) * ∏ p ∈ N.primeFactors, ratio p := by
        congr 1
        conv_rhs => rw [h2]
        push_cast
        ring

/-! ## Bounding a product of abundancy factors over few odd primes -/

lemma prod_ratio_base (b : ℕ) :
    ∀ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q ∧ b ≤ q) → S.card ≤ 0 → ∏ q ∈ S, ratio q ≤ 1 := by
  intro S _ h
  rw [Finset.card_eq_zero.mp (Nat.le_zero.mp h)]
  simp

/-- If there is no prime in `[b, p)` then every prime `≥ b` is `≥ p`. -/
lemma prime_ge_of_no_prime_between {b p : ℕ} (h : ∀ q < p, b ≤ q → ¬ q.Prime) :
    ∀ q, q.Prime → b ≤ q → p ≤ q := by
  intro q hq hbq
  by_contra hlt
  push_neg at hlt
  exact h q hlt hbq hq

/-- Inductive step: if `p` is the least prime `≥ b`, and every set of at most `k` primes `≥ p+1`
has `∏ ratio ≤ C`, then every set of at most `k+1` primes `≥ b` has `∏ ratio ≤ ratio p * C`. -/
lemma prod_ratio_step {b p k : ℕ} {C : ℚ} (hp : p.Prime)
    (hmin : ∀ q, q.Prime → b ≤ q → p ≤ q) (hC : 1 ≤ C)
    (ih : ∀ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q ∧ p + 1 ≤ q) → S.card ≤ k →
      ∏ q ∈ S, ratio q ≤ C) :
    ∀ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q ∧ b ≤ q) → S.card ≤ k + 1 →
      ∏ q ∈ S, ratio q ≤ ratio p * C := by
  intro S hS hcard
  have hrp : 1 ≤ ratio p := one_le_ratio hp.two_le
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.prod_empty]
    nlinarith
  · set m := S.min' hne with hm
    have hmS : m ∈ S := S.min'_mem hne
    obtain ⟨hmp, hbm⟩ := hS m hmS
    have hpm : p ≤ m := hmin m hmp hbm
    have hSe : ∀ q ∈ S.erase m, Nat.Prime q ∧ p + 1 ≤ q := by
      intro q hq
      have hq' := Finset.mem_of_mem_erase hq
      have hne' : q ≠ m := Finset.ne_of_mem_erase hq
      have : m ≤ q := S.min'_le q hq'
      exact ⟨(hS q hq').1, by omega⟩
    have hcard' : (S.erase m).card ≤ k := by
      have h1 := Finset.card_erase_of_mem hmS
      have h2 : 1 ≤ S.card := Finset.card_pos.mpr hne
      omega
    have hprod : ∏ q ∈ S, ratio q = ratio m * ∏ q ∈ S.erase m, ratio q :=
      (Finset.mul_prod_erase S _ hmS).symm
    have h1 : ∏ q ∈ S.erase m, ratio q ≤ C := ih _ hSe hcard'
    have h0 : (0 : ℚ) ≤ ∏ q ∈ S.erase m, ratio q :=
      Finset.prod_nonneg (fun i hi => ratio_nonneg (hSe i hi).1.two_le)
    rw [hprod]
    have := ratio_antitone hp.two_le hpm
    nlinarith

/-- **Key estimate.** For a set of at most twenty odd primes, `∏ p/(p-1) < 4`.
The extremal case is the set of the first twenty odd primes, for which the product
equals `≈ 3.9668`. -/
lemma prod_ratio_lt_four (S : Finset ℕ) (hS : ∀ q ∈ S, Nat.Prime q ∧ 3 ≤ q)
    (hcard : S.card ≤ 20) : ∏ q ∈ S, ratio q < 4 := by
  have c0 : ∀ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q ∧ 74 ≤ q) → S.card ≤ 0 →
      ∏ q ∈ S, ratio q ≤ 1 := prod_ratio_base 74
  have c1 := prod_ratio_step (b := 72) (p := 73) (k := 0) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c0
  have c2 := prod_ratio_step (b := 68) (p := 71) (k := 1) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c1
  have c3 := prod_ratio_step (b := 62) (p := 67) (k := 2) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c2
  have c4 := prod_ratio_step (b := 60) (p := 61) (k := 3) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c3
  have c5 := prod_ratio_step (b := 54) (p := 59) (k := 4) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c4
  have c6 := prod_ratio_step (b := 48) (p := 53) (k := 5) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c5
  have c7 := prod_ratio_step (b := 44) (p := 47) (k := 6) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c6
  have c8 := prod_ratio_step (b := 42) (p := 43) (k := 7) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c7
  have c9 := prod_ratio_step (b := 38) (p := 41) (k := 8) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c8
  have c10 := prod_ratio_step (b := 32) (p := 37) (k := 9) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c9
  have c11 := prod_ratio_step (b := 30) (p := 31) (k := 10) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c10
  have c12 := prod_ratio_step (b := 24) (p := 29) (k := 11) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c11
  have c13 := prod_ratio_step (b := 20) (p := 23) (k := 12) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c12
  have c14 := prod_ratio_step (b := 18) (p := 19) (k := 13) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c13
  have c15 := prod_ratio_step (b := 14) (p := 17) (k := 14) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c14
  have c16 := prod_ratio_step (b := 12) (p := 13) (k := 15) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c15
  have c17 := prod_ratio_step (b := 8) (p := 11) (k := 16) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c16
  have c18 := prod_ratio_step (b := 6) (p := 7) (k := 17) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c17
  have c19 := prod_ratio_step (b := 4) (p := 5) (k := 18) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c18
  have c20 := prod_ratio_step (b := 3) (p := 3) (k := 19) (by norm_num)
    (prime_ge_of_no_prime_between (by decide)) (by norm_num [ratio]) c19
  refine lt_of_le_of_lt (c20 S hS hcard) ?_
  norm_num [ratio]

/-! ## Hagis–Lord Proposition 2 (second part) -/

/-- In a coprime pair of equal parity with a positive member, both members are odd:
two coprime numbers cannot both be even. -/
lemma odd_of_coprime_sameParity {m n : ℕ} (hco : Nat.Coprime m n)
    (hpar : m % 2 = n % 2) : Odd m ∧ Odd n := by
  have h : m % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · exfalso
      have hdm : 2 ∣ m := Nat.dvd_of_mod_eq_zero h0
      have hdn : 2 ∣ n := Nat.dvd_of_mod_eq_zero (hpar ▸ h0)
      have hd : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd hdm hdn
      rw [Nat.Coprime] at hco
      rw [hco] at hd
      norm_num at hd
    · exact h1
  exact ⟨Nat.odd_iff.mpr h, Nat.odd_iff.mpr (by omega)⟩

/-- **Hagis–Lord, Proposition 2 (second part).**
If `(m, n)` is a betrothed (quasi-amicable) pair with `gcd(m, n) = 1` whose two members
have the same parity, then both members are odd and the product `m * n` has at least
twenty-one distinct prime factors.

Proof sketch: coprimality forces both members to be odd (so `m * n` is odd), while
`σ₁(m·n) = σ₁(m)·σ₁(n) = (m+n+1)² > 4mn`, i.e. `m·n` has abundancy index `> 4`.
The rational abundancy bound `σ₁(N) ≤ N ∏_{p ∣ N} p/(p-1)`, together with the fact that
the product of `p/(p-1)` over any twenty odd primes is at most
`∏_{i=1}^{20} q_i/(q_i-1) ≈ 3.9668 < 4` (`q_i` the `i`-th odd prime), then forces at least
twenty-one distinct prime factors.

This is the *exact*, unconditional statement.  The far larger numerical lower bounds for
such a pair that appear in the literature come from computer searches; they are
deliberately **not** asserted here. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ}
    (h : IsBetrothedPair m n) (hco : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm0, hn0, hsm, hsn⟩ := h
  obtain ⟨hoddm, hoddn⟩ := odd_of_coprime_sameParity hco hpar
  refine ⟨hoddm, hoddn, ?_⟩
  set N := m * n with hNdef
  have hNpos : 0 < N := Nat.mul_pos hm0 hn0
  have hNne : N ≠ 0 := hNpos.ne'
  have hNodd : Odd N := hoddm.mul hoddn
  -- `σ₁(N) = (m + n + 1)^2`
  have hmul : sigmaOne N = (m + n + 1) ^ 2 := by
    have hmm := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hco
    simp only [sigmaOne] at hsm hsn ⊢
    rw [hNdef, hmm, hsm, hsn]
    ring
  by_contra hlt
  push_neg at hlt
  have hcard : N.primeFactors.card ≤ 20 := by omega
  have hS : ∀ q ∈ N.primeFactors, Nat.Prime q ∧ 3 ≤ q := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ N := Nat.dvd_of_mem_primeFactors hq
    have hNmod : N % 2 = 1 := Nat.odd_iff.mp hNodd
    have hq2 : q ≠ 2 := by
      rintro rfl
      omega
    exact ⟨hqp, by have := hqp.two_le; omega⟩
  have h1 : (sigmaOne N : ℚ) ≤ N * ∏ q ∈ N.primeFactors, ratio q := sigmaOne_le_mul_prod_ratio hNne
  have h2 : ∏ q ∈ N.primeFactors, ratio q < 4 := prod_ratio_lt_four _ hS hcard
  have hNQ : (0 : ℚ) < N := by exact_mod_cast hNpos
  -- the abundancy index of `N` exceeds `4`
  have h4 : (4 : ℚ) * N < (sigmaOne N : ℚ) := by
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
    have hnQ : (0 : ℚ) < n := by exact_mod_cast hn0
    have : ((sigmaOne N : ℕ) : ℚ) = ((m : ℚ) + n + 1) ^ 2 := by rw [hmul]; push_cast; ring
    rw [this, hNdef]
    push_cast
    nlinarith [sq_nonneg ((m : ℚ) - n)]
  nlinarith

/-!
## Separation from historical computational lower bounds

The theorem above is the exact, unconditional part of Hagis-Lord Proposition 2: it is proved
here in full from the definitions, with no computational input beyond primality checks for the
numbers below `74` and exact rational arithmetic with the twenty fractions `q/(q-1)`.

By contrast, the numerical lower bounds on a hypothetical coprime same-parity betrothed pair
that appear in the literature come from finite computer searches.  No such bound is asserted,
used, or verified anywhere in this file; the statements above stand on their own.
-/

end BetrothedNumbers
end Brockian

