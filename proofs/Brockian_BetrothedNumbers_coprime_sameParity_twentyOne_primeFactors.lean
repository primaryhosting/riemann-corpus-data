/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals the sum of the two numbers plus one. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-! ### The elementary abundancy bound `σ(N)/N ≤ ∏_{p ∣ N} p/(p-1)` -/

/-- For a prime `p` and any exponent `k`, the geometric sum `1 + p + ⋯ + p ^ k`
is bounded by `p ^ k * (p / (p - 1))`. -/
lemma geom_sum_le_prime_pow_mul {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (p : ℝ) ^ i) ≤ (p : ℝ) ^ k * ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hne : (p : ℝ) ≠ 1 := ne_of_gt hp1
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [geom_sum_eq hne]
  rw [div_le_iff₀ hpos]
  have : (p : ℝ) ^ k * ((p : ℝ) / ((p : ℝ) - 1)) * ((p : ℝ) - 1) = (p : ℝ) ^ (k + 1) := by
    field_simp
    ring
  rw [this]
  have h1 : (0 : ℝ) < 1 := one_pos
  nlinarith [pow_pos (lt_trans zero_lt_one hp1) (k + 1)]

/-- The abundancy index of `N` is bounded by the product of `p / (p - 1)` over the
distinct prime factors of `N`. -/
lemma sigma_one_le_mul_prod_primeFactors {N : ℕ} (hN : N ≠ 0) :
    (σ 1 N : ℝ) ≤ (N : ℝ) * ∏ p ∈ N.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hσ : (σ 1 N : ℝ)
      = ∏ p ∈ N.primeFactors, ∑ i ∈ Finset.range (N.factorization p + 1), (p : ℝ) ^ i := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hN]
    push_cast
    rfl
  have hNprod : (N : ℝ) = ∏ p ∈ N.primeFactors, (p : ℝ) ^ (N.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    push_cast
    rfl
  rw [hσ, hNprod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod ?_ ?_
  · intro p _
    positivity
  · intro p hp
    exact geom_sum_le_prime_pow_mul (Nat.prime_of_mem_primeFactors hp) _

/-! ### The twenty smallest odd primes -/

/-- The set of the twenty smallest odd primes (all odd primes `≤ 73`). -/
def smallOddPrimes : Finset ℕ :=
  {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73}

lemma smallOddPrimes_card : smallOddPrimes.card = 20 := by decide

lemma mem_smallOddPrimes_of_lt {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hlt : p < 74) :
    p ∈ smallOddPrimes := by
  have key : ∀ q ∈ Finset.range 74, Nat.Prime q → q % 2 = 1 → q ∈ smallOddPrimes := by decide
  exact key p (Finset.mem_range.2 hlt) hp (Nat.odd_iff.1 hodd)

lemma le_of_mem_smallOddPrimes {p : ℕ} (hp : p ∈ smallOddPrimes) : 3 ≤ p ∧ p ≤ 73 := by
  fin_cases hp <;> exact ⟨by norm_num, by norm_num⟩

lemma prod_smallOddPrimes_lt_four :
    ∏ p ∈ smallOddPrimes, (p : ℝ) / ((p : ℝ) - 1) < 4 := by
  rw [show smallOddPrimes =
      (⟨[3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73],
        by decide⟩ : Finset ℕ) from by decide]
  simp only [Finset.prod_mk, Multiset.map_coe, Multiset.prod_coe, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  norm_num

/-- For any finite set of at most twenty odd primes, the product of `p / (p - 1)` is at
most the corresponding product over the twenty smallest odd primes. -/
lemma prod_odd_primes_le_prod_smallOddPrimes {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ Odd p) (hcard : S.card ≤ 20) :
    ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) ≤ ∏ p ∈ smallOddPrimes, (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  set g : ℕ → ℝ := fun p => (p : ℝ) / ((p : ℝ) - 1) with hg
  set A := S ∩ smallOddPrimes with hA
  set B := S \ smallOddPrimes with hB
  have hAsub : A ⊆ smallOddPrimes := Finset.inter_subset_right
  have hgpos : ∀ p ∈ S, 0 < g p := by
    intro p hp
    obtain ⟨hprime, hodd⟩ := hS p hp
    have h3 : 3 ≤ p := by
      have h2 := hprime.two_le
      have := Nat.odd_iff.1 hodd
      omega
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact div_pos (by linarith) this
  -- split the product
  have hsplit : ∏ p ∈ S, g p = (∏ p ∈ A, g p) * ∏ p ∈ B, g p := by
    rw [hA, hB, Finset.prod_inter_mul_prod_diff]
  -- bound the large primes
  have hBle : ∏ p ∈ B, g p ≤ (73 / 72 : ℝ) ^ B.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => (hgpos p (Finset.mem_sdiff.1 hp).1).le) ?_
    intro p hp
    have hpS : p ∈ S := (Finset.mem_sdiff.1 hp).1
    have hpn : p ∉ smallOddPrimes := (Finset.mem_sdiff.1 hp).2
    obtain ⟨hprime, hodd⟩ := hS p hpS
    have h73 : 74 ≤ p := by
      by_contra hlt
      exact hpn (mem_smallOddPrimes_of_lt hprime hodd (by omega))
    have hr : (74 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h73
    rw [hg, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  -- the leftover small primes
  have hleft : (73 / 72 : ℝ) ^ (smallOddPrimes \ A).card ≤ ∏ p ∈ smallOddPrimes \ A, g p := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => by norm_num) ?_
    intro p hp
    obtain ⟨h3, h73⟩ := le_of_mem_smallOddPrimes (Finset.mem_sdiff.1 hp).1
    have hr3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
    have hr73 : (p : ℝ) ≤ 73 := by exact_mod_cast h73
    rw [hg, div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hcards : B.card ≤ (smallOddPrimes \ A).card := by
    have h1 : A.card + B.card = S.card := Finset.card_inter_add_card_sdiff S smallOddPrimes
    have h2 : (smallOddPrimes \ A).card + A.card = smallOddPrimes.card :=
      Finset.card_sdiff_add_card_eq_card hAsub
    rw [smallOddPrimes_card] at h2
    omega
  have hpowmono : (73 / 72 : ℝ) ^ B.card ≤ (73 / 72 : ℝ) ^ (smallOddPrimes \ A).card :=
    pow_le_pow_right₀ (by norm_num) hcards
  have hApos : 0 < ∏ p ∈ A, g p :=
    Finset.prod_pos fun p hp => hgpos p (Finset.mem_of_mem_inter_left hp)
  calc ∏ p ∈ S, g p = (∏ p ∈ A, g p) * ∏ p ∈ B, g p := hsplit
    _ ≤ (∏ p ∈ A, g p) * (73 / 72 : ℝ) ^ (smallOddPrimes \ A).card := by
        refine mul_le_mul_of_nonneg_left ?_ hApos.le
        exact le_trans hBle hpowmono
    _ ≤ (∏ p ∈ A, g p) * ∏ p ∈ smallOddPrimes \ A, g p :=
        mul_le_mul_of_nonneg_left hleft hApos.le
    _ = ∏ p ∈ smallOddPrimes, g p := by
        rw [mul_comm]; exact Finset.prod_sdiff hAsub

/-- If an odd number `N` has abundancy index exceeding `4`, then it has at least twenty-one
distinct prime factors. -/
lemma twentyOne_le_card_primeFactors_of_abundancy {N : ℕ} (hN : N ≠ 0) (hodd : Odd N)
    (habund : 4 * N < σ 1 N) : 21 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ 20 := by omega
  have hS : ∀ p ∈ N.primeFactors, p.Prime ∧ Odd p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hprime, hprime.odd_of_ne_two ?_⟩
    rintro rfl
    have h2 : (2 : ℕ) ∣ N := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.odd_iff] at hodd
    omega
  have h1 : (σ 1 N : ℝ) ≤ (N : ℝ) * ∏ p ∈ N.primeFactors, (p : ℝ) / ((p : ℝ) - 1) :=
    sigma_one_le_mul_prod_primeFactors hN
  have h2 : ∏ p ∈ N.primeFactors, (p : ℝ) / ((p : ℝ) - 1) < 4 :=
    lt_of_le_of_lt (prod_odd_primes_le_prod_smallOddPrimes hS hcard) prod_smallOddPrimes_lt_four
  have h3 : (4 : ℝ) * N < (σ 1 N : ℝ) := by exact_mod_cast habund
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  nlinarith [h1, h2, h3]

/-! ### The main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If `(m, n)` is a betrothed
(quasi-amicable) pair with `m` and `n` coprime and of the same parity, then both are odd
and their product has at least twenty-one distinct prime factors. -/
theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ}
    (h : IsBetrothedPair m n) (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, hσm, hσn⟩ := h
  have hoddm : Odd m := by
    rw [Nat.odd_iff]
    by_contra hcon
    have hm2 : m % 2 = 0 := by omega
    have hn2 : n % 2 = 0 := by omega
    have : 2 ∣ Nat.gcd m n := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hm2) (Nat.dvd_of_mod_eq_zero hn2)
    rw [hcop] at this
    omega
  have hoddn : Odd n := by
    rw [Nat.odd_iff]; rw [Nat.odd_iff] at hoddm; omega
  refine ⟨hoddm, hoddn, ?_⟩
  have hprod_odd : Odd (m * n) := hoddm.mul hoddn
  have hNne : m * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hσmul : σ 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hσm, hσn]
  have habund : 4 * (m * n) < σ 1 (m * n) := by
    rw [hσmul]
    have hz : (4 : ℤ) * ((m : ℤ) * n) < ((m : ℤ) + n + 1) * ((m : ℤ) + n + 1) := by
      nlinarith [sq_nonneg ((m : ℤ) - n), Int.natCast_nonneg m, Int.natCast_nonneg n]
    exact_mod_cast hz
  exact twentyOne_le_card_primeFactors_of_abundancy hNne hprod_odd habund

/-!
### Historical computational lower bounds (not formalized)

The theorem above is the exact, unconditional statement.  It should be clearly distinguished
from the *computational* lower bounds in the literature on betrothed (quasi-amicable) numbers,
such as the statements that a same-parity betrothed pair must exceed various explicit search
bounds.  Those bounds rest on exhaustive machine searches and are **not** formalized here; only
the exact arithmetic statement is proved.
-/

end Brockian.BetrothedNumbers

