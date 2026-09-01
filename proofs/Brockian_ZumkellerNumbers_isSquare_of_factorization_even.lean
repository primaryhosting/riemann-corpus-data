import Mathlib

namespace Brockian.ZumkellerNumbers

open Finset

def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- If every prime exponent in the factorization of `t` is even, then `t` is a square. -/
lemma isSquare_of_factorization_even {t : ℕ} (ht : t ≠ 0)
    (h : ∀ p, Even (t.factorization p)) : IsSquare t := by
  have key : ∏ p ∈ t.primeFactors, p ^ t.factorization p = t := by
    simpa [Nat.support_factorization, Finsupp.prod] using Nat.factorization_prod_pow_eq_self ht
  refine ⟨∏ p ∈ t.primeFactors, p ^ (t.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← key]
  refine Finset.prod_congr rfl ?_
  intro p _
  rw [← pow_add]
  congr 1
  obtain ⟨c, hc⟩ := h p
  omega

/-- Every prime exponent in the factorization of a square is even. -/
lemma factorization_even_of_isSquare {t : ℕ} (h : IsSquare t) (p : ℕ) :
    Even (t.factorization p) := by
  obtain ⟨m, rfl⟩ := h
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [Nat.factorization_mul hm hm]
    exact ⟨_, rfl⟩

/-- A positive natural number has an odd number of divisors iff it is a square. -/
lemma odd_card_divisors_iff_isSquare {t : ℕ} (ht : t ≠ 0) :
    Odd t.divisors.card ↔ IsSquare t := by
  rw [Nat.card_divisors ht]
  constructor
  · intro h
    refine isSquare_of_factorization_even ht ?_
    intro p
    by_cases hp : p ∈ t.primeFactors
    · have h2 : ¬ (2 ∣ ∏ x ∈ t.primeFactors, (t.factorization x + 1)) := by
        simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using h
      have : ¬ (2 ∣ (t.factorization p + 1)) :=
        fun hd => h2 (hd.trans (Finset.dvd_prod_of_mem _ hp))
      rcases Nat.even_or_odd (t.factorization p) with he | ho
      · exact he
      · obtain ⟨c, hc⟩ := ho
        exact absurd ⟨c + 1, by omega⟩ this
    · have hz : t.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
      simp [hz]
  · intro h
    have hev : ∀ p, Even (t.factorization p) := factorization_even_of_isSquare h
    rw [Nat.odd_iff, ← Nat.not_even_iff, even_iff_two_dvd]
    intro hdvd
    obtain ⟨p, hp, hpd⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff _).1 hdvd
    obtain ⟨c, hc⟩ := hev p
    omega

/-- The odd divisors of `n = 2 ^ k * t` (with `t` odd) are exactly the divisors of `t`. -/
lemma filter_odd_divisors {n k t : ℕ} (hn : n ≠ 0) (hkt : n = 2 ^ k * t) (hto : Odd t) :
    {d ∈ n.divisors | Odd d} = t.divisors := by
  have ht : t ≠ 0 := by
    rintro rfl; simp at hkt; exact hn hkt
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hodd⟩
    refine ⟨?_, ht⟩
    rw [hkt] at hd
    have hcop : Nat.Coprime d (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hd)
  · rintro ⟨hd, -⟩
    refine ⟨⟨hd.trans ⟨2 ^ k, by rw [hkt]; ring⟩, hn⟩, hto.of_dvd_nat hd⟩

theorem sigma_odd_iff_square_or_two_mul_square (n : ℕ) (hn : 0 < n) :
    Odd (∑ d ∈ n.divisors, d) ↔ (IsSquare n ∨ IsSquare (2 * n)) := by
  obtain ⟨k, t, hto, hkt⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hn0 : n ≠ 0 := hn.ne'
  have ht : t ≠ 0 := by rintro rfl; simp at hkt; exact hn0 hkt
  have hstep : Odd (∑ d ∈ n.divisors, d) ↔ IsSquare t := by
    rw [Finset.odd_sum_iff_odd_card_odd (fun d => d), filter_odd_divisors hn0 hkt hto,
      odd_card_divisors_iff_isSquare ht]
  rw [hstep]
  have ht2 : t.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.two_dvd_ne_zero, Nat.odd_iff] using hto)
  have hfac : ∀ p, p ≠ 2 → n.factorization p = t.factorization p := by
    intro p hp
    rw [hkt, Nat.factorization_mul (by positivity) ht]
    simp [Nat.Prime.factorization_pow Nat.prime_two, Ne.symm hp]
  constructor
  · intro hsq
    obtain ⟨m, hm⟩ := hsq
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      exact ⟨2 ^ j * m, by rw [hkt, hm, hj]; ring⟩
    · right
      exact ⟨2 ^ (j + 1) * m, by rw [hkt, hm, hj]; ring⟩
  · intro h
    refine isSquare_of_factorization_even ht ?_
    intro p
    by_cases hp2 : p = 2
    · subst hp2; simp [ht2]
    · rw [← hfac p hp2]
      rcases h with h | h
      · exact factorization_even_of_isSquare h p
      · have : (2 * n).factorization p = n.factorization p := by
          rw [Nat.factorization_mul (by norm_num) hn0]
          simp [Nat.Prime.factorization Nat.prime_two, Ne.symm hp2]
        rw [← this]
        exact factorization_even_of_isSquare h p

end Brockian.ZumkellerNumbers

