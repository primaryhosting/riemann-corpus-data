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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Betrothed (quasi-amicable) pairs -/

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals `m + n + 1`; equivalently `s(m) = n + 1` and `s(n) = m + 1`, where `s`
denotes the sum of the proper divisors. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-! ## The rational abundancy bound

The abundancy index `σ₁(N) / N` is bounded above by the Euler product
`∏_{p ∣ N} p / (p - 1)` taken over the distinct prime divisors of `N`. -/

/-- For a prime power, `σ₁(p ^ e) ≤ p ^ e * (p / (p - 1))` over `ℚ`. -/
theorem sigma_one_prime_pow_le {p e : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ e) : ℚ)) ≤ (p : ℚ) ^ e * ((p : ℚ) / ((p : ℚ) - 1)) := by
  have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hne : (p : ℚ) ≠ 1 := by linarith
  have hpos : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rw [geom_sum_eq hne, mul_div_assoc']
  gcongr
  rw [pow_succ]
  linarith

/-- **The rational abundancy bound.** The abundancy index of `N` is at most
`∏_{p ∣ N} p / (p - 1)`. -/
theorem sigma_one_le_prod_primeFactors {N : ℕ} (hN : N ≠ 0) :
    ((σ 1 N : ℚ)) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, (p : ℚ) / ((p : ℚ) - 1) := by
  have hmul : σ 1 N = N.factorization.prod fun p k => σ 1 (p ^ k) :=
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hN
  rw [Finsupp.prod, Nat.support_factorization] at hmul
  have hNeq : (N : ℚ) = ∏ p ∈ N.primeFactors, (p : ℚ) ^ (N.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    ring
  rw [hmul, hNeq, ← Finset.prod_mul_distrib]
  push_cast
  refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
  exact sigma_one_prime_pow_le (Nat.prime_of_mem_primeFactors hp)

/-! ## An elementary bound on Euler products over sets of odd primes -/

/-- The first twenty odd primes. -/
def firstTwentyOddPrimes : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73}

theorem card_firstTwentyOddPrimes : firstTwentyOddPrimes.card = 20 := by decide

/-- The Euler product over the first twenty odd primes is (just) below `4`; its value is
`3.9654...`.  Adjoining the twenty-first odd prime `79` would push it above `4`, which is
exactly why twenty-one prime factors are needed. -/
theorem prod_firstTwentyOddPrimes_lt_four :
    (∏ p ∈ firstTwentyOddPrimes, (p : ℚ) / ((p : ℚ) - 1)) < 4 := by
  rw [show firstTwentyOddPrimes =
      (⟨[3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73],
        by decide⟩ : Finset ℕ) from by decide, Finset.prod_mk]
  norm_num [Multiset.prod_coe]

/-- An odd prime that is not among the first twenty odd primes is at least `79`. -/
theorem odd_prime_notMem_ge {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : p ∉ firstTwentyOddPrimes) : 79 ≤ p := by
  by_contra hlt
  push_neg at hlt
  have key : ∀ q < 79, Nat.Prime q → q % 2 = 1 → q ∈ firstTwentyOddPrimes := by decide
  exact h (key p hlt hp (Nat.odd_iff.mp hodd))

/-- If `S` is a set of at most twenty odd primes, then `∏_{p ∈ S} p / (p - 1) < 4`.

The proof compares `S` with the set `Q` of the first twenty odd primes: the factors coming
from primes of `S` outside `Q` are each at most `79 / 78`, and there are enough spare
factors in `Q \ S`, each at least `79 / 78`, to absorb them. -/
theorem prod_lt_four_of_card_le_twenty {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ Odd p) (hcard : S.card ≤ 20) :
    (∏ p ∈ S, (p : ℚ) / ((p : ℚ) - 1)) < 4 := by
  classical
  set Q := firstTwentyOddPrimes with hQ
  set f : ℕ → ℚ := fun p => (p : ℚ) / ((p : ℚ) - 1) with hf
  have hQbound : ∀ q ∈ Q, 2 ≤ q ∧ q ≤ 79 := by decide
  have hfQ : ∀ q ∈ Q, (79 : ℚ) / 78 ≤ f q := by
    intro q hq
    obtain ⟨h2, h79⟩ := hQbound q hq
    have h2' : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast h2
    have h79' : (q : ℚ) ≤ 79 := by exact_mod_cast h79
    rw [hf, div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hfS : ∀ p ∈ S, (0 : ℚ) < f p := by
    intro p hp
    obtain ⟨hprime, hoddp⟩ := hS p hp
    have h2 := hprime.two_le
    have hm := Nat.odd_iff.mp hoddp
    have h3 : 3 ≤ p := by omega
    have h3' : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
    rw [hf]
    exact div_pos (by linarith) (by linarith)
  have hsub : S ∩ Q ⊆ Q := Finset.inter_subset_right
  have hsplitS : (∏ p ∈ S ∩ Q, f p) * (∏ p ∈ S \ Q, f p) = ∏ p ∈ S, f p := by
    rw [mul_comm, ← Finset.sdiff_inter_self_left S Q]
    exact Finset.prod_sdiff Finset.inter_subset_left
  have hsplitQ : (∏ p ∈ Q \ (S ∩ Q), f p) * (∏ p ∈ S ∩ Q, f p) = ∏ p ∈ Q, f p :=
    Finset.prod_sdiff hsub
  have hcards : (S \ Q).card ≤ (Q \ (S ∩ Q)).card := by
    have h1 : (S ∩ Q).card + (S \ Q).card = S.card := Finset.card_inter_add_card_sdiff S Q
    have h2 : (Q \ (S ∩ Q)).card = Q.card - (S ∩ Q).card := by
      rw [Finset.card_sdiff]
      congr 1
      simp [Finset.inter_assoc]
    have h3 : Q.card = 20 := card_firstTwentyOddPrimes
    omega
  have hBle : (∏ p ∈ S \ Q, f p) ≤ ((79 : ℚ) / 78) ^ (S \ Q).card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => (hfS p (Finset.mem_sdiff.mp hp).1).le)
      (fun p hp => ?_)
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hpS, hpQ⟩ := hp
    obtain ⟨hprime, hoddp⟩ := hS p hpS
    have h79 : (79 : ℚ) ≤ (p : ℚ) := by exact_mod_cast odd_prime_notMem_ge hprime hoddp hpQ
    rw [hf, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hpow : ((79 : ℚ) / 78) ^ (S \ Q).card ≤ ((79 : ℚ) / 78) ^ (Q \ (S ∩ Q)).card :=
    pow_le_pow_right₀ (by norm_num) hcards
  have hQle : ((79 : ℚ) / 78) ^ (Q \ (S ∩ Q)).card ≤ ∏ p ∈ Q \ (S ∩ Q), f p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q _ => by norm_num)
      (fun q hq => hfQ q (Finset.mem_sdiff.mp hq).1)
  have hApos : (0 : ℚ) < ∏ p ∈ S ∩ Q, f p :=
    Finset.prod_pos (fun p hp => hfS p (Finset.mem_inter.mp hp).1)
  calc ∏ p ∈ S, f p = (∏ p ∈ S ∩ Q, f p) * (∏ p ∈ S \ Q, f p) := hsplitS.symm
    _ ≤ (∏ p ∈ S ∩ Q, f p) * (∏ p ∈ Q \ (S ∩ Q), f p) :=
        mul_le_mul_of_nonneg_left (le_trans hBle (le_trans hpow hQle)) hApos.le
    _ = ∏ p ∈ Q, f p := by rw [mul_comm]; exact hsplitQ
    _ < 4 := prod_firstTwentyOddPrimes_lt_four

/-- An odd number whose abundancy index exceeds `4` has at least twenty-one distinct
prime factors. -/
theorem twentyOne_primeFactors_of_odd_of_four_mul_lt_sigma {N : ℕ} (hodd : Odd N)
    (h : 4 * N < σ 1 N) : 21 ≤ N.primeFactors.card := by
  by_contra hc
  push_neg at hc
  have hN : N ≠ 0 := by rintro rfl; simp at hodd
  have hNpos : (0 : ℚ) < (N : ℚ) := by
    have : 0 < N := Nat.pos_of_ne_zero hN
    exact_mod_cast this
  have hodds : ∀ p ∈ N.primeFactors, Nat.Prime p ∧ Odd p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hprime, ?_⟩
    rcases hprime.eq_two_or_odd' with rfl | hodd'
    · exfalso
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      rw [Nat.odd_iff] at hodd
      omega
    · exact hodd'
  have hprod := prod_lt_four_of_card_le_twenty hodds (by omega)
  have h1 : (4 * N : ℚ) < (σ 1 N : ℚ) := by exact_mod_cast h
  have h2 := sigma_one_le_prod_primeFactors hN
  have h3 : (N : ℚ) * ∏ p ∈ N.primeFactors, (p : ℚ) / ((p : ℚ) - 1) < (N : ℚ) * 4 :=
    mul_lt_mul_of_pos_left hprod hNpos
  linarith

/-! ## Main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If `(m, n)` is a betrothed
(quasi-amicable) pair whose members are coprime and of the same parity, then both members
are odd and the product `m * n` has at least twenty-one distinct prime factors.

The argument: coprimality rules out both members being even, so both are odd.  Since
`m` and `n` are coprime, `σ₁(m * n) = σ₁(m) σ₁(n) = (m + n + 1)² > 4 m n`, so the odd
number `m * n` has abundancy index greater than `4`; by the rational abundancy bound its
Euler product `∏_{p ∣ mn} p / (p - 1)` exceeds `4`, which is impossible with twenty or
fewer odd prime factors, since the product over the first twenty odd primes is only
`3.9654...`. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ}
    (h : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : Even m ↔ Even n) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  have hmodd : Odd m := by
    rw [Nat.odd_iff]
    by_contra hc
    have hem : Even m := by rw [Nat.even_iff]; omega
    have hen : Even n := hpar.mp hem
    have hdvd : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd hem.two_dvd hen.two_dvd
    rw [hcop] at hdvd
    omega
  have hnodd : Odd n := by
    rw [Nat.odd_iff]
    by_contra hc
    have hen : Even n := by rw [Nat.even_iff]; omega
    have hem : Even m := hpar.mpr hen
    rw [Nat.even_iff] at hem
    rw [Nat.odd_iff] at hmodd
    omega
  refine ⟨hmodd, hnodd, ?_⟩
  have hprododd : Odd (m * n) := hmodd.mul hnodd
  have hsig : σ 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [(ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop, hsm, hsn]
  have hlt : 4 * (m * n) < σ 1 (m * n) := by
    rw [hsig]
    nlinarith [sq_nonneg ((m : ℤ) - n)]
  exact twentyOne_primeFactors_of_odd_of_four_mul_lt_sigma hprododd hlt

/-! ## Historical computational lower bounds (not formalized)

The theorem above is the *exact* statement proved here.  It should be distinguished from
the purely computational lower bounds reported in the literature on quasi-amicable
(betrothed) pairs, such as exhaustive searches showing that no betrothed pair below a
given search bound has its two members of the same parity.  Such bounds depend on
large-scale computation and are **not** formalized in this file; nothing below or above
asserts them. -/

end BetrothedNumbers
end Brockian

