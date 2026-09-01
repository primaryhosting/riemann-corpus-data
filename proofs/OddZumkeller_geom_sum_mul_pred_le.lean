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

namespace OddZumkeller

/-- A positive natural number `n` is a *Zumkeller number* if its set of divisors can be split
into two parts having the same sum. -/
def Zumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d

/-- Geometric-sum bound: `(1 + p + ⋯ + p ^ k) * (p - 1) ≤ p ^ (k + 1)`. -/
lemma geom_sum_mul_pred_le (p k : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range (k + 1), p ^ i) * (p - 1) ≤ p ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : (∑ i ∈ Finset.range (k + 1 + 1), p ^ i)
        = (∑ i ∈ Finset.range (k + 1), p ^ i) + p ^ (k + 1) := Finset.sum_range_succ _ _
    have e2 : p ^ (k + 1 + 1) = p ^ (k + 1) * p := pow_succ p (k + 1)
    have h3 : p ^ (k + 1) * (p - 1) ≤ p ^ (k + 1) * p - p ^ (k + 1) := by
      cases p with
      | zero => omega
      | succ q => rw [Nat.mul_sub]; simp
    have hpk : p ^ (k + 1) ≤ p ^ (k + 1) * p := Nat.le_mul_of_pos_right _ hp
    rw [e1, e2, add_mul]
    omega

/-- The key multiplicative estimate: `σ(n) * ∏_{p ∣ n} (p - 1) ≤ n * ∏_{p ∣ n} p`,
which is the integral form of `σ(n) / n < ∏_{p ∣ n} p / (p - 1)`. -/
lemma sum_divisors_mul_prod_pred_le (n : ℕ) :
    (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
      ≤ n * ∏ p ∈ n.primeFactors, p := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      have hpf : (p ^ k).primeFactors = {p} := by
        rw [Nat.primeFactors_pow _ hk.ne', hp.primeFactors]
      rw [hpf, Nat.sum_divisors_prime_pow hp]
      simp only [Finset.prod_singleton]
      calc (∑ i ∈ Finset.range (k + 1), p ^ i) * (p - 1)
          ≤ p ^ (k + 1) := geom_sum_mul_pred_le p k hp.one_lt.le
        _ = p ^ k * p := pow_succ p k
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hdisj : Disjoint a.primeFactors b.primeFactors := Nat.Coprime.disjoint_primeFactors hab
      rw [hab.sum_divisors_mul, Nat.primeFactors_mul ha0 hb0, Finset.prod_union hdisj,
        Finset.prod_union hdisj]
      calc ((∑ d ∈ a.divisors, d) * ∑ d ∈ b.divisors, d) *
            ((∏ p ∈ a.primeFactors, (p - 1)) * ∏ p ∈ b.primeFactors, (p - 1))
          = ((∑ d ∈ a.divisors, d) * ∏ p ∈ a.primeFactors, (p - 1)) *
            ((∑ d ∈ b.divisors, d) * ∏ p ∈ b.primeFactors, (p - 1)) := by ring
        _ ≤ (a * ∏ p ∈ a.primeFactors, p) * (b * ∏ p ∈ b.primeFactors, p) :=
            Nat.mul_le_mul iha ihb
        _ = a * b * ((∏ p ∈ a.primeFactors, p) * ∏ p ∈ b.primeFactors, p) := by ring

/-- A Zumkeller number is perfect or abundant: `2 * n ≤ σ n`. -/
lemma two_mul_le_sum_divisors_of_zumkeller {n : ℕ} (h : Zumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hn, S, hS, hsum⟩ := h
  have hsplit : (∑ d ∈ n.divisors \ S, d) + (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have hn_le : n ≤ ∑ d ∈ S, d := by
    by_cases hnS : n ∈ S
    · simpa using Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hnS
    · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, hnS⟩
      have := Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hmem'
      simp only at this
      omega
  omega

/-- Every prime factor of an odd number is at least `3`. -/
lemma three_le_of_mem_primeFactors_odd {n p : ℕ} (hodd : Odd n) (hp : p ∈ n.primeFactors) :
    3 ≤ p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    rintro rfl
    have h1 : n % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have := hpp.two_le
  omega

/-- **Main structural result.** An odd Zumkeller number has at least three distinct prime
factors. -/
theorem three_le_card_primeFactors {n : ℕ} (hodd : Odd n) (h : Zumkeller n) :
    3 ≤ n.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : n.primeFactors.card ≤ 2 := by omega
  have hn : 0 < n := h.1
  have hsig : 2 * n ≤ ∑ d ∈ n.divisors, d := two_mul_le_sum_divisors_of_zumkeller h
  have hkey := sum_divisors_mul_prod_pred_le n
  have hstep : 2 * n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p :=
    le_trans (Nat.mul_le_mul_right _ hsig) hkey
  have hmain : 2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ p ∈ n.primeFactors, p := by
    have : n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) ≤ n * ∏ p ∈ n.primeFactors, p := by
      calc n * (2 * ∏ p ∈ n.primeFactors, (p - 1))
          = 2 * n * ∏ p ∈ n.primeFactors, (p - 1) := by ring
        _ ≤ n * ∏ p ∈ n.primeFactors, p := hstep
    exact Nat.le_of_mul_le_mul_left this hn
  interval_cases hc : n.primeFactors.card
  · -- no prime factors
    rw [Finset.card_eq_zero] at hc
    rw [hc] at hmain
    simp at hmain
  · -- one prime factor
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hp3 : 3 ≤ p := three_le_of_mem_primeFactors_odd hodd (by rw [hp]; exact Finset.mem_singleton_self p)
    rw [hp] at hmain
    simp only [Finset.prod_singleton] at hmain
    omega
  · -- two prime factors
    obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc
    have hp3 : 3 ≤ p := three_le_of_mem_primeFactors_odd hodd (by rw [hset]; simp)
    have hq3 : 3 ≤ q := three_le_of_mem_primeFactors_odd hodd (by rw [hset]; simp)
    rw [hset] at hmain
    rw [Finset.prod_pair hpq, Finset.prod_pair hpq] at hmain
    -- both are odd primes, hence one of them is at least 5
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    have hqq : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    have hp4 : p ≠ 4 := by rintro rfl; exact absurd hpp (by decide)
    have hq4 : q ≠ 4 := by rintro rfl; exact absurd hqq (by decide)
    have hp5 : 5 ≤ p ∨ 5 ≤ q := by omega
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hmain
    rcases hp5 with h5 | h5 <;> nlinarith [hmain]

/-- The divisors of `945`. -/
lemma divisors_945 : (945 : ℕ).divisors =
    ({1, 3, 5, 7, 9, 15, 21, 27, 35, 45, 63, 105, 135, 189, 315, 945} : Finset ℕ) := by
  decide

/-- `945` is an odd Zumkeller number, and it has exactly three distinct prime factors,
so the bound in `OddZumkellerFrom3Structure` is sharp. -/
theorem zumkeller_945 : Odd (945 : ℕ) ∧ Zumkeller 945 ∧ (945 : ℕ).primeFactors.card = 3 := by
  refine ⟨by decide, ⟨by norm_num, {15, 945}, ?_, ?_⟩, ?_⟩
  · rw [divisors_945]; decide
  · rw [divisors_945]; decide
  · have h : (945 : ℕ).primeFactors = {3, 5, 7} := by simp [Nat.primeFactors]
    rw [h]; decide

end OddZumkeller

/-- **The structure statement for odd Zumkeller numbers**: every odd Zumkeller number has at
least three distinct prime factors.  (This is sharp: `945 = 3 ^ 3 * 5 * 7` is an odd Zumkeller
number with exactly three distinct prime factors, see `OddZumkeller.zumkeller_945`.) -/
def OddZumkellerFrom3Structure : Prop :=
  ∀ n : ℕ, Odd n → OddZumkeller.Zumkeller n → 3 ≤ n.primeFactors.card

theorem oddZumkellerFrom3Structure : OddZumkellerFrom3Structure :=
  fun _ hodd h => OddZumkeller.three_le_card_primeFactors hodd h

