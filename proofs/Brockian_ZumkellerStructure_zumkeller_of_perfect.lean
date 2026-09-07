import Mathlib

namespace Brockian.ZumkellerStructure

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n).
Matches `Brockian.ZumkellerNumbers.Zumkeller` verbatim. -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- Every perfect number is Zumkeller: take `S = {n}`. -/
theorem zumkeller_of_perfect {n : ℕ} (hn : 0 < n) (h : ∑ d ∈ n.divisors, d = 2 * n) :
    Zumkeller n := by
  refine ⟨{n}, ?_, ?_⟩
  · simpa using Nat.mem_divisors_self n hn.ne'
  · simp [h]

/-- Every divisor of an odd number is odd. -/
lemma odd_of_dvd_odd {n d : ℕ} (hodd : Odd n) (hd : d ∣ n) : Odd d := by
  obtain ⟨c, rfl⟩ := hd
  exact (Nat.odd_mul.mp hodd).1

/-- For odd `n`, the sum of divisors has the same parity as the number of divisors. -/
lemma sum_divisors_mod_two {n : ℕ} (hodd : Odd n) :
    (∑ d ∈ n.divisors, d) % 2 = n.divisors.card % 2 := by
  rw [Finset.sum_nat_mod]
  rw [Finset.sum_congr rfl
    (fun d hd => Nat.odd_iff.mp (odd_of_dvd_odd hodd (Nat.dvd_of_mem_divisors hd)))]
  simp

/-- A nonzero square has an odd number of divisors. -/
lemma odd_card_divisors_of_isSquare {n : ℕ} (hn : n ≠ 0) (hsq : IsSquare n) :
    Odd n.divisors.card := by
  obtain ⟨k, rfl⟩ := hsq
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  rw [Nat.card_divisors hn]
  refine Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one ?_
  intro p _
  have hfac : (k * k).factorization p = 2 * k.factorization p := by
    rw [Nat.factorization_mul hk hk]; simp [two_mul]
  rw [hfac]
  exact ⟨k.factorization p, by ring⟩

/-- An odd Zumkeller number is not a perfect square: being Zumkeller forces `sigma n` to be
even, while for an odd square all divisors are odd and there is an odd number of them, so
`sigma n` would be odd. -/
theorem odd_zumkeller_not_square {n : ℕ} (hodd : Odd n) (h : Zumkeller n) : ¬ IsSquare n := by
  intro hsq
  obtain ⟨S, _, hsum⟩ := h
  have hn : n ≠ 0 := by rintro rfl; simp at hodd
  have h1 : (∑ d ∈ n.divisors, d) % 2 = 0 := by omega
  have h2 := sum_divisors_mod_two hodd
  have h3 := Nat.odd_iff.mp (odd_card_divisors_of_isSquare hn hsq)
  omega

/-- A deficient number (one with `sigma n < 2 * n`) is never Zumkeller: a candidate subset
`S` of the divisors can neither contain `n` (then `2 * ∑ S ≥ 2 * n > sigma n`) nor omit it
(then `∑ S + n ≤ sigma n`, so `2 * ∑ S ≤ 2 * sigma n - 2 * n < sigma n`). -/
theorem not_zumkeller_of_deficient (n : ℕ) (hn : 0 < n)
    (h : ∑ d ∈ n.divisors, d < 2 * n) : ¬ Zumkeller n := by
  rintro ⟨S, hS, hsum⟩
  have hnd : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  by_cases hmem : n ∈ S
  · have : n ≤ ∑ d ∈ S, d :=
      Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) hmem
    omega
  · have h1 : ∑ d ∈ insert n S, d ≤ ∑ d ∈ n.divisors, d :=
      Finset.sum_le_sum_of_subset (Finset.insert_subset hnd hS)
    rw [Finset.sum_insert hmem] at h1
    omega

/-- The half-sum characterization of Zumkeller numbers is equivalent to the
equal-partition form: a subset of the divisors whose sum equals the sum of its complement. -/
theorem zumkeller_iff_partition (n : ℕ) :
    Zumkeller n ↔ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d := by
  constructor
  · rintro ⟨S, hS, h⟩
    have hsum : (∑ d ∈ n.divisors \ S, d) + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
      Finset.sum_sdiff hS
    exact ⟨S, hS, by omega⟩
  · rintro ⟨S, hS, h⟩
    have hsum : (∑ d ∈ n.divisors \ S, d) + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
      Finset.sum_sdiff hS
    exact ⟨S, hS, by omega⟩
theorem zumkeller_mul_coprime {n m : ℕ} (h : Zumkeller n) (hm : 0 < m)
    (hco : n.Coprime m) : Zumkeller (n * m) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨∅, by simp, by simp⟩
  obtain ⟨S, hSsub, hSsum⟩ := h
  have hSdvd : ∀ d ∈ S, d ∣ n := fun d hd => (Nat.mem_divisors.mp (hSsub hd)).1
  set T : Finset ℕ := (S ×ˢ m.divisors).image (fun p => p.1 * p.2) with hT
  have hinj : ∀ p ∈ S ×ˢ m.divisors, ∀ q ∈ S ×ˢ m.divisors,
      p.1 * p.2 = q.1 * q.2 → p = q := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd hEq
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
    have hbm : b ∣ m := (Nat.mem_divisors.mp hb).1
    have hdm : d ∣ m := (Nat.mem_divisors.mp hd).1
    have han : a ∣ n := hSdvd a ha
    have hcn : c ∣ n := hSdvd c hc
    have hEq' : a * b = c * d := hEq
    have hac : a = c := by
      have h1 : a ∣ c :=
        Nat.Coprime.dvd_of_dvd_mul_right
          (Nat.Coprime.coprime_dvd_left han (Nat.Coprime.coprime_dvd_right hdm hco))
          (hEq' ▸ Dvd.intro b rfl)
      have h2 : c ∣ a :=
        Nat.Coprime.dvd_of_dvd_mul_right
          (Nat.Coprime.coprime_dvd_left hcn (Nat.Coprime.coprime_dvd_right hbm hco))
          (hEq' ▸ Dvd.intro d rfl)
      exact Nat.dvd_antisymm h1 h2
    subst hac
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos han hn
    have hbd : b = d := Nat.eq_of_mul_eq_mul_left hapos hEq'
    simp [hbd]
  have hsub : T ⊆ (n * m).divisors := by
    intro x hx
    rw [hT, Finset.mem_image] at hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
    rw [Finset.mem_product] at hab
    exact Nat.mem_divisors.mpr
      ⟨mul_dvd_mul (hSdvd a hab.1) (Nat.mem_divisors.mp hab.2).1,
        Nat.mul_ne_zero hn.ne' hm.ne'⟩
  refine ⟨T, hsub, ?_⟩
  have hsumT : ∑ d ∈ T, d = (∑ d ∈ S, d) * (∑ e ∈ m.divisors, e) := by
    rw [hT, Finset.sum_image hinj, Finset.sum_product, Finset.sum_mul_sum]
  rw [hsumT, hco.sum_divisors_mul, ← mul_assoc, hSsum]

/-- The sum of a geometric progression `1 + p + ⋯ + p ^ k` is less than `2 * p ^ k`
for `p ≥ 2`. -/
lemma geom_sum_lt_two_mul_pow (p k : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range (k + 1), p ^ i < 2 * p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : 2 * p ^ k ≤ p ^ (k + 1) := by
        have := Nat.mul_le_mul_right (p ^ k) hp
        simpa [pow_succ, Nat.mul_comm] using this
      rw [Finset.sum_range_succ]
      have : 2 * p ^ (k + 1) = p ^ (k + 1) + p ^ (k + 1) := by ring
      omega

/-- Prime powers are deficient: `σ (p ^ k) < 2 * p ^ k`. -/
lemma sum_divisors_prime_pow_lt (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ k).divisors, d < 2 * p ^ k := by
  rw [Nat.sum_divisors_prime_pow hp]
  exact geom_sum_lt_two_mul_pow p k hp.two_le

theorem not_zumkeller_prime_pow (p k : ℕ) (hp : p.Prime) : ¬ Zumkeller (p ^ k) := by
  rintro ⟨S, hS, hsum⟩
  have hN0 : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hNmem : p ^ k ∈ (p ^ k).divisors := Nat.mem_divisors_self _ hN0
  have hlt := sum_divisors_prime_pow_lt p k hp
  by_cases hNS : p ^ k ∈ S
  · have hle : p ^ k ≤ ∑ d ∈ S, d :=
      Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) hNS
    omega
  · have hsub : S ⊆ (p ^ k).divisors.erase (p ^ k) := Finset.subset_erase.2 ⟨hS, hNS⟩
    have h1 : ∑ d ∈ S, d ≤ ∑ d ∈ (p ^ k).divisors.erase (p ^ k), d :=
      Finset.sum_le_sum_of_subset hsub
    have h2 : p ^ k + ∑ d ∈ (p ^ k).divisors.erase (p ^ k), d = ∑ d ∈ (p ^ k).divisors, d :=
      Finset.add_sum_erase _ (fun d => d) hNmem
    omega

/-- If the sum of divisors of `n` is odd, then `n` is not Zumkeller. -/
theorem not_zumkeller_of_sigma_odd (n : ℕ) (h : Odd (∑ d ∈ n.divisors, d)) : ¬ Zumkeller n := by
  rintro ⟨S, -, hS⟩
  rw [← hS] at h
  exact (Nat.not_odd_iff_even.mpr ⟨∑ d ∈ S, d, by ring⟩) h

/-- Any `x < 2 ^ k` is the sum of the powers of two given by its binary digits. -/
lemma sum_range_testBit (k : ℕ) : ∀ x : ℕ, x < 2 ^ k →
    ∑ i ∈ Finset.range k, (if x.testBit i then 2 ^ i else 0) = x := by
  induction k with
  | zero => intro x hx; simp at hx ⊢; omega
  | succ n ih =>
    intro x hx
    rw [Finset.sum_range_succ']
    have hdiv : x / 2 < 2 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      calc x < 2 ^ (n + 1) := hx
        _ = 2 ^ n * 2 := by ring
    have hIH := ih (x / 2) hdiv
    have hstep : ∀ i ∈ Finset.range n,
        (if x.testBit (i + 1) then 2 ^ (i + 1) else 0)
          = 2 * (if (x / 2).testBit i then 2 ^ i else 0) := by
      intro i _
      rw [Nat.testBit_add_one]
      by_cases h : (x / 2).testBit i <;> simp [h, pow_succ, Nat.mul_comm]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hIH]
    have h0 : (if x.testBit 0 then 2 ^ 0 else 0) = x % 2 := by
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
    rw [h0]
    omega

/-- The geometric sum of powers of two. -/
lemma sum_range_two_pow_succ (k : ℕ) : (∑ i ∈ Finset.range (k + 1), 2 ^ i) + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; omega

/-- The sum of the divisors of `2 ^ k * p` for an odd prime `p`. -/
lemma sum_divisors_two_pow_mul_prime (k p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ∑ d ∈ (2 ^ k * p).divisors, d = (∑ i ∈ Finset.range (k + 1), 2 ^ i) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := by
    refine Nat.Coprime.pow_left k ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rw [Nat.odd_iff] at hodd
    omega
  have hmul := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply] at hmul
  rw [hmul]
  congr 1
  · exact Nat.sum_divisors_prime_pow Nat.prime_two
  · rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]; omega

/-- If `p` is an odd prime with `p < 2 ^ (k + 1)`, then `2 ^ k * p` is a Zumkeller number:
its divisors split into two parts of equal sum.

The hypothesis `1 ≤ k` is part of the requested statement; the proof does not need it. -/
theorem zumkeller_two_pow_mul_prime (k : ℕ) (p : ℕ) (hk : 1 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (hlt : p < 2 ^ (k + 1)) : Zumkeller (2 ^ k * p) := by
  obtain ⟨m, hm⟩ : ∃ m, p + 1 = 2 * m := by
    rw [Nat.odd_iff] at hodd; exact ⟨(p + 1) / 2, by omega⟩
  have hp1 : 1 < p := hp.one_lt
  have hm1 : 1 ≤ m := by omega
  set A : ℕ := ∑ i ∈ Finset.range (k + 1), 2 ^ i with hAdef
  have hA : A + 1 = 2 ^ (k + 1) := sum_range_two_pow_succ k
  have hA1 : 1 ≤ A := by
    have : 2 ^ (k + 1) ≥ 2 := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set T : ℕ := A * m with hTdef
  set a : ℕ := T / p with hadef
  set b : ℕ := T % p with hbdef
  have hab : p * a + b = T := Nat.div_add_mod T p
  have hbp : b < p := Nat.mod_lt _ (by omega)
  have hblt : b < 2 ^ (k + 1) := lt_trans hbp hlt
  have halt : a < 2 ^ (k + 1) := by
    rw [hadef, Nat.div_lt_iff_lt_mul (by omega), ← hA]
    have h2 : 2 * (A * m) < 2 * ((A + 1) * p) := by
      have hAm : A * (2 * m) = A * (p + 1) := by rw [hm]
      nlinarith [hA1, hp1]
    have : A * m < (A + 1) * p := by omega
    simpa [hTdef] using this
  -- the two families of divisors
  set F1 : Finset ℕ := (Finset.range (k + 1)).filter (fun i => a.testBit i) with hF1
  set F2 : Finset ℕ := (Finset.range (k + 1)).filter (fun i => b.testBit i) with hF2
  have hsum1 : ∑ i ∈ F1, 2 ^ i = a := by
    rw [hF1, Finset.sum_filter]
    exact sum_range_testBit (k + 1) a halt
  have hsum2 : ∑ i ∈ F2, 2 ^ i = b := by
    rw [hF2, Finset.sum_filter]
    exact sum_range_testBit (k + 1) b hblt
  have hinj1 : Set.InjOn (fun i => 2 ^ i * p) (F1 : Set ℕ) := by
    intro x _ y _ h
    simp only at h
    have h2 : (2:ℕ) ^ x = 2 ^ y := Nat.eq_of_mul_eq_mul_right (by omega) h
    exact Nat.pow_right_injective (le_refl 2) h2
  have hinj2 : Set.InjOn (fun i => (2:ℕ) ^ i) (F2 : Set ℕ) := by
    intro x _ y _ h
    exact Nat.pow_right_injective (le_refl 2) h
  set S1 : Finset ℕ := F1.image (fun i => 2 ^ i * p) with hS1
  set S2 : Finset ℕ := F2.image (fun i => 2 ^ i) with hS2
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    rw [hS1, Finset.mem_image] at hx1
    rw [hS2, Finset.mem_image] at hx2
    obtain ⟨i, _, hi⟩ := hx1
    obtain ⟨j, _, hj⟩ := hx2
    have heq : 2 ^ i * p = 2 ^ j := by rw [hi, hj]
    have hdvd : p ∣ 2 ^ j := Dvd.intro_left _ heq
    have : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    rw [Nat.odd_iff] at hodd
    omega
  refine ⟨S1 ∪ S2, ?_, ?_⟩
  · intro x hx
    rw [Nat.mem_divisors]
    have hn : 2 ^ k * p ≠ 0 := by positivity
    refine ⟨?_, hn⟩
    rcases Finset.mem_union.mp hx with h | h
    · rw [hS1, Finset.mem_image] at h
      obtain ⟨i, hi, rfl⟩ := h
      rw [hF1, Finset.mem_filter, Finset.mem_range] at hi
      exact Nat.mul_dvd_mul (pow_dvd_pow 2 (by omega)) dvd_rfl
    · rw [hS2, Finset.mem_image] at h
      obtain ⟨i, hi, rfl⟩ := h
      rw [hF2, Finset.mem_filter, Finset.mem_range] at hi
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) p
  · rw [Finset.sum_union hdisj, hS1, hS2, Finset.sum_image hinj1, Finset.sum_image hinj2,
      ← Finset.sum_mul, hsum1, hsum2, sum_divisors_two_pow_mul_prime k p hp hodd, ← hAdef]
    have hfin : a * p + b = A * m := by rw [mul_comm a p, hab, hTdef]
    calc 2 * (a * p + b) = 2 * (A * m) := by rw [hfin]
      _ = A * (2 * m) := by ring
      _ = A * (p + 1) := by rw [hm]

open Finset

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

end Brockian.ZumkellerStructure
