/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
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

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers with `σ m = σ n = m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- For a prime power, `σ(p ^ a) * (p - 1) = p ^ (a+1) - 1 ≤ p ^ a * p`. -/
lemma sigma_primePow_mul_pred_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigma 1 (p ^ a) * (p - 1) ≤ p ^ a * p := by
  have h2 := hp.two_le
  have hgeom : ∀ b : ℕ, (∑ i ∈ Finset.range (b + 1), p ^ i) * (p - 1) ≤ p ^ b * p := by
    intro b
    induction b with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, add_mul]
        have key : p ^ (k + 1) * (p - 1) + p ^ (k + 1) = p ^ (k + 1) * p := by
          obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
          simp; ring
        have hpk : p ^ k * p = p ^ (k + 1) := (pow_succ _ k).symm
        omega
  have hs : sigma 1 (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [hs]
  exact hgeom a

/-- Multiplying the prime-power estimates together over the factorization of `N`:
`σ(N) * ∏_{p ∣ N} (p - 1) ≤ N * ∏_{p ∣ N} p`, i.e. `σ(N)/N ≤ ∏_{p ∣ N} p/(p-1)`. -/
lemma sigma_mul_prod_pred_le {N : ℕ} (hN : N ≠ 0) :
    sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1) ≤ N * ∏ p ∈ N.primeFactors, p := by
  have h1 : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) := by
    rw [(isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hN]; rfl
  have h2 : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hN]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
  calc sigma 1 N * ∏ p ∈ N.primeFactors, (p - 1)
      = ∏ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p) * (p - 1)) := by
        rw [h1, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ N.primeFactors, (p ^ N.factorization p * p) :=
        Finset.prod_le_prod' fun q hq =>
          sigma_primePow_mul_pred_le (Nat.prime_of_mem_primeFactors hq) _
    _ = N * ∏ p ∈ N.primeFactors, p := by rw [Finset.prod_mul_distrib, h2]

/-- For a set of at most three primes, `∏ p ≤ 4 * ∏ (p - 1)`; the extremal case
`{2, 3, 5}` gives `∏ p/(p-1) = 15/4 < 4`. -/
lemma prod_le_four_mul_prod_pred {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, p ≤ 4 * ∏ p ∈ S, (p - 1) := by
  have h5 : ∀ r : ℕ, r.Prime → 4 ≤ r → 5 ≤ r := by
    intro r hr h
    rcases eq_or_lt_of_le h with rfl | h'
    · exact absurd hr (by norm_num)
    · omega
  have key2 : ∀ p q : ℕ, 2 ≤ p → 3 ≤ q → p * q ≤ 4 * ((p - 1) * (q - 1)) := by
    intro p q hp hq
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 2 := ⟨p - 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 3 := ⟨q - 3, by omega⟩
    show (a + 2) * (b + 3) ≤ 4 * ((a + 1) * (b + 2))
    nlinarith [Nat.zero_le (a * b)]
  have key3 : ∀ p q r : ℕ, 2 ≤ p → 3 ≤ q → 5 ≤ r →
      p * q * r ≤ 4 * ((p - 1) * ((q - 1) * (r - 1))) := by
    intro p q r hp hq hr
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 2 := ⟨p - 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 3 := ⟨q - 3, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, r = c + 5 := ⟨r - 5, by omega⟩
    show (a + 2) * (b + 3) * (c + 5) ≤ 4 * ((a + 1) * ((b + 2) * (c + 4)))
    nlinarith [Nat.zero_le (a * b), Nat.zero_le (a * c), Nat.zero_le (b * c),
      Nat.zero_le (a * b * c)]
  have hc : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hc with h | h | h | h
  · rw [Finset.card_eq_zero] at h; subst h; simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have ha := (hS a (by simp)).two_le
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have ha := (hS a (by simp)).two_le
    have hb := (hS b (by simp)).two_le
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · have := key2 a b ha (by omega); linarith
    · have := key2 b a hb (by omega); linarith
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have hpa := hS a (by simp)
    have hpb := hS b (by simp)
    have hpc := hS c (by simp)
    have ha := hpa.two_le
    have hb := hpb.two_le
    have hcc := hpc.two_le
    have hprod : ∀ f : ℕ → ℕ, ∏ x ∈ ({a, b, c} : Finset ℕ), f x = f a * (f b * f c) := by
      intro f
      rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton]
    rw [hprod (fun x => x), hprod (fun x => x - 1)]
    rcases lt_trichotomy a b with h1 | h1 | h1 <;> rcases lt_trichotomy a c with h2 | h2 | h2 <;>
      rcases lt_trichotomy b c with h3 | h3 | h3 <;>
      first
        | omega
        | (first
            | (have := key3 a b c ha (by omega) (h5 c hpc (by omega)); linarith)
            | (have := key3 a c b ha (by omega) (h5 b hpb (by omega)); linarith)
            | (have := key3 b a c hb (by omega) (h5 c hpc (by omega)); linarith)
            | (have := key3 b c a hb (by omega) (h5 a hpa (by omega)); linarith)
            | (have := key3 c a b hcc (by omega) (h5 b hpb (by omega)); linarith)
            | (have := key3 c b a hcc (by omega) (h5 a hpa (by omega)); linarith))

/-- Key intermediate lemma: a number of abundancy greater than `4` has at least four
distinct prime factors, since three distinct primes can only give `∏ p/(p-1) ≤ 15/4`. -/
lemma four_le_card_primeFactors_of_abundancy {N : ℕ} (hN : 0 < N) (h : 4 * N < sigma 1 N) :
    4 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ 3 := by omega
  set Q := ∏ p ∈ N.primeFactors, (p - 1) with hQ
  set P := ∏ p ∈ N.primeFactors, p with hP
  have hQpos : 0 < Q := by
    rw [hQ]
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h1 : 4 * N * Q < sigma 1 N * Q := (Nat.mul_lt_mul_right hQpos).mpr h
  have h2 := sigma_mul_prod_pred_le hN.ne'
  have h3 := prod_le_four_mul_prod_pred (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have h4 : N * P ≤ N * (4 * Q) := Nat.mul_le_mul_left _ h3
  nlinarith

/-- **Hagis–Lord, Proposition 2.**  If `m` and `n` are coprime betrothed numbers, then
`m * n` has at least four distinct prime factors.

The proof: coprimality and multiplicativity of `σ` give `σ(mn) = (m+n+1)^2 > 4mn`, so
`mn` has abundancy `> 4`; but a number with at most three distinct prime factors has
abundancy `< ∏ p/(p-1) ≤ 2 · (3/2) · (5/4) = 15/4 < 4`. -/
theorem coprime_pair_four_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hmn : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, -, hsm, hsn⟩ := h
  refine four_le_card_primeFactors_of_abundancy (Nat.mul_pos hm hn) ?_
  rw [isMultiplicative_sigma.map_mul_of_coprime hmn, hsm, hsn]
  rcases le_total m n with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    nlinarith [Nat.zero_le (m * d), Nat.zero_le (d * d)]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    nlinarith [Nat.zero_le (n * d), Nat.zero_le (d * d)]

end Brockian.BetrothedNumbers

