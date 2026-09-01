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

set_option grind.warning false

def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

def Quasiperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 n = 2 * n + 1

/-- For an odd `p`, the geometric sum `1 + p + ⋯ + p ^ e` is odd iff `e` is even. -/
lemma even_of_odd_geom_sum {p e : ℕ} (hp : Odd p)
    (h : Odd (∑ k ∈ Finset.range (e + 1), p ^ k)) : Even e := by
  rw [Nat.odd_iff, Finset.sum_nat_mod] at h
  have hk : ∀ k ∈ Finset.range (e + 1), p ^ k % 2 = 1 := fun k _ => Nat.odd_iff.mp hp.pow
  rw [Finset.sum_congr rfl hk] at h
  simp at h
  rw [Nat.even_iff]
  omega

/-- A positive natural number all of whose prime exponents are even is a square. -/
lemma isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod fun p k => p ^ (k / 2), ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [← Finsupp.prod_mul]
  refine Finsupp.prod_congr fun p _ => ?_
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := h p
  omega

theorem quasiperfect_isSquare_or_two_mul_square {n : ℕ} (h : Quasiperfect n) :
    IsSquare n ∨ ∃ m : ℕ, n = 2 * m ^ 2 := by
  obtain ⟨hn, hs⟩ := h
  have hn0 : n ≠ 0 := hn.ne'
  have hodd : Odd (sigma1 n) := ⟨n, by omega⟩
  have hprod : sigma1 n =
      ∏ p ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k :=
    Nat.sum_divisors hn0
  -- every odd prime occurs to an even power
  have hfac : ∀ p, p ≠ 2 → Even (n.factorization p) := by
    intro p hp2
    by_cases hmem : p ∈ n.primeFactors
    · have hdvd : (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) ∣ sigma1 n := by
        rw [hprod]; exact Finset.dvd_prod_of_mem _ hmem
      obtain ⟨c, hc⟩ := hdvd
      rw [hc] at hodd
      exact even_of_odd_geom_sum
        ((Nat.prime_of_mem_primeFactors hmem).odd_of_ne_two hp2) (Nat.odd_mul.mp hodd).1
    · have : n.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hmem
      simp [this]
  rcases Nat.even_or_odd (n.factorization 2) with h2 | h2
  · left
    refine isSquare_of_factorization_even hn0 fun p => ?_
    by_cases hp : p = 2
    · subst hp; exact h2
    · exact hfac p hp
  · right
    have hdvd2 : 2 ∣ n := by
      have : (2:ℕ).Prime := Nat.prime_two
      have hpos : 0 < n.factorization 2 := by
        rcases h2 with ⟨k, hk⟩; omega
      exact (Nat.Prime.dvd_iff_one_le_factorization this hn0).mpr hpos
    set m := n / 2 with hm
    have hnm : n = 2 * m := (Nat.mul_div_cancel' hdvd2).symm
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0] at hnm; omega
    have hmfac : ∀ p, Even (m.factorization p) := by
      intro p
      have hfd : m.factorization = n.factorization - (2:ℕ).factorization := by
        rw [hm]; exact Nat.factorization_div hdvd2
      by_cases hp : p = 2
      · subst hp
        have : m.factorization 2 = n.factorization 2 - 1 := by
          rw [hfd]; simp [Nat.Prime.factorization Nat.prime_two]
        rw [this, Nat.even_sub (by rcases h2 with ⟨k, hk⟩; omega)]
        simpa using h2
      · have : m.factorization p = n.factorization p := by
          rw [hfd]
          simp [Nat.Prime.factorization Nat.prime_two, Ne.symm hp]
        rw [this]
        exact hfac p hp
    obtain ⟨r, hr⟩ := isSquare_of_factorization_even hm0 hmfac
    exact ⟨r, by rw [hnm, hr]; ring⟩

