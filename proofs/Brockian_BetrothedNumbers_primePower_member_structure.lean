/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and the
sum of the divisors of each equals `m + n + 1` (equivalently, the sum of the *proper* divisors of
each one is the other one plus one). -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

lemma IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  refine ⟨hn, hm, hne.symm, ?_, ?_⟩ <;> omega

/-! ### Elementary facts about `σ 1` -/

/-- `σ 1 p = p + 1` for a prime `p`. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simpa [Finset.sum_range_succ, Nat.add_comm] using this

/-- Crude upper bound `2 * σ 1 k ≤ k * (k + 1)`, since every divisor of `k` lies in `[1, k]`. -/
lemma two_mul_sigma_one_le (k : ℕ) : 2 * σ 1 k ≤ k * (k + 1) := by
  rw [sigma_one_apply]
  have hsub : k.divisors ⊆ Finset.range (k + 1) := fun d hd => by
    simp only [Finset.mem_range]; exact Nat.lt_succ_of_le (Nat.divisor_le hd)
  have h1 := Finset.sum_le_sum_of_subset (f := _root_.id) hsub
  have h2 : (∑ i ∈ Finset.range (k + 1), i) * 2 = (k + 1) * k := by
    simpa using Finset.sum_range_id_mul_two (k + 1)
  have h3 : k * (k + 1) = (k + 1) * k := Nat.mul_comm _ _
  simp only [_root_.id] at h1
  omega

/-- If `q = 3 * r` with `r ≥ 2` and `r ≠ 3`, then `1, 3, r, 3 * r` are four distinct divisors
of `q`, hence `σ 1 q ≥ 4 + r + 3 * r`. -/
lemma sigma_one_three_mul_ge {r : ℕ} (hr : 2 ≤ r) (hr3 : r ≠ 3) :
    1 + 3 + r + 3 * r ≤ σ 1 (3 * r) := by
  rw [sigma_one_apply]
  have hq : 3 * r ≠ 0 := by omega
  have hsub : ({1, 3, r, 3 * r} : Finset ℕ) ⊆ (3 * r).divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [Nat.mem_divisors, hq]
  have h1 := Finset.sum_le_sum_of_subset (f := _root_.id) hsub
  simp only [_root_.id] at h1
  have hsum : ∑ d ∈ ({1, 3, r, 3 * r} : Finset ℕ), d = 1 + 3 + r + 3 * r := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    ring
  omega

/-! ### Geometric sums -/

/-- For odd `p`, the geometric sum `1 + p + ⋯ + p ^ (k - 1)` has the same parity as `k`. -/
lemma geom_sum_mod_two {p : ℕ} (hp : Odd p) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
      omega

lemma geom_sum_two (b : ℕ) : (∑ i ∈ Finset.range b, 2 ^ i) + 1 = 2 ^ b := by
  induction b with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ]; omega

/-! ### The partner of a prime power -/

/-- If `p ^ a` belongs to a betrothed pair with partner `n`, then
`n + 1 = 1 + p + ⋯ + p ^ (a - 1)`. -/
lemma partner_eq {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    n + 1 = ∑ i ∈ Finset.range a, p ^ i := by
  obtain ⟨-, -, -, h1, -⟩ := h
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ] at h1
  omega

/-! ### The main structure theorem -/

/-- **Hagis–Lord, Proposition 4.**  If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair with partner `n`, then `p` is odd, `a` is odd with `a > 3`, and the
partner `n` is even. -/
theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime)
    (h : IsBetrothedPair (p ^ a) n) : Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  obtain ⟨hm0, hn0, hne, hsm, hsn⟩ := h
  have hpair : IsBetrothedPair (p ^ a) n := ⟨hm0, hn0, hne, hsm, hsn⟩
  have hgs : n + 1 = ∑ i ∈ Finset.range a, p ^ i := partner_eq hp hpair
  -- `a ≥ 1`, say `a = b + 1`
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := by
    cases a with
    | zero => simp at hgs
    | succ b => exact ⟨b, rfl⟩
  rw [geom_sum_succ] at hgs
  -- `b ≥ 1`, say `b = c + 1`
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp only [Finset.range_zero, Finset.sum_empty, Nat.mul_zero] at hgs; omega
    · exact hb
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  -- name the geometric sum `G = 1 + p + ⋯ + p ^ c`; the partner is `n = p * G`
  obtain ⟨G, hG⟩ : ∃ G, ∑ i ∈ Finset.range (c + 1), p ^ i = G := ⟨_, rfl⟩
  rw [hG] at hgs
  have hnG : n = p * G := by omega
  have hGc : G = p * (∑ i ∈ Finset.range c, p ^ i) + 1 := by rw [← hG, geom_sum_succ]
  have hcop : Nat.Coprime p G := by rw [hGc]; simp
  have hG0 : 0 < G := by rw [hGc]; positivity
  -- the sum-of-divisors of the partner factors as `(p + 1) * σ 1 G`
  have hsplit : σ 1 n = (p + 1) * σ 1 G := by
    rw [hnG, isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp]
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · -- `p = 2` is impossible
    exfalso
    have hGpow : G + 1 = 2 ^ (c + 1) := by rw [← hG]; exact geom_sum_two _
    have hpow : (2 : ℕ) ^ (c + 1 + 1) = 2 * (G + 1) := by rw [pow_succ, hGpow]; ring
    -- the defining equation becomes `3 * σ 1 G = 4 * G + 3`
    have key : 3 * σ 1 G = 4 * G + 3 := by
      rw [hsplit, hpow] at hsn
      omega
    -- hence `3 ∣ G`
    have h3 : 3 ∣ G := by omega
    obtain ⟨r, rfl⟩ := h3
    rcases Nat.lt_or_ge r 2 with hr | hr
    · interval_cases r
      · omega
      · -- `G = 3`
        have h31 : σ 1 (3 * 1) = 4 := by decide
        omega
    · rcases eq_or_ne r 3 with rfl | hr3
      · -- `G = 9` would force `2 ^ (c + 1) = 10`
        have h5 : (5 : ℕ) ∣ 2 ^ (c + 1) := ⟨2, by omega⟩
        have h52 : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h5
        omega
      · -- four distinct divisors of `G` already overshoot
        have := sigma_one_three_mul_ge hr hr3
        omega
  · -- `p` is odd
    have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
    -- `σ 1 n` is even, since `p + 1` divides it
    have heven : Even (σ 1 n) := by
      rw [hsplit]; exact (hpodd.add_one).mul_right _
    have hnEven : Even n := by
      have h1 : σ 1 n % 2 = 0 := Nat.even_iff.mp heven
      have h2 : p ^ (c + 1 + 1) % 2 = 1 := Nat.odd_iff.mp hpodd.pow
      rw [Nat.even_iff]
      omega
    -- hence `G` is even, hence `c` is odd, hence `a = c + 2` is odd
    have hGeven : Even G := by
      have hev : Even (p * G) := hnG ▸ hnEven
      rcases Nat.even_mul.mp hev with hh | hh
      · exact absurd hh (Nat.not_even_iff_odd.mpr hpodd)
      · exact hh
    have hGeven' : G % 2 = 0 := Nat.even_iff.mp hGeven
    have hcodd : c % 2 = 1 := by
      have hpar := geom_sum_mod_two hpodd (c + 1)
      rw [hG] at hpar
      omega
    refine ⟨hpodd, by rw [Nat.odd_iff]; omega, ?_, hnEven⟩
    -- it remains to rule out `a = 3`, i.e. `c = 1`
    by_contra hcon
    have hc1 : c = 1 := by omega
    subst hc1
    have hGval : G = 1 + p := by rw [← hG]; simp [Finset.sum_range_succ]
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have e1 : σ 1 n = (p + 1) * σ 1 (1 + p) := by rw [hsplit, hGval]
    rw [e1, hnG, hGval] at hsn
    have hkey : (p + 1) * σ 1 (1 + p) = (p + 1) * (p ^ 2 + 1) := by rw [hsn]; ring
    have hsig : σ 1 (1 + p) = p ^ 2 + 1 := Nat.eq_of_mul_eq_mul_left (by omega) hkey
    have hbound := two_mul_sigma_one_le (1 + p)
    rw [hsig] at hbound
    have hple : p ≤ 3 := by nlinarith
    have hpeq : p = 3 := by omega
    subst hpeq
    have h4 : σ 1 (1 + 3) = 7 := by decide
    rw [h4] at hsig
    norm_num at hsig

/-- Sanity check (non-vacuity): `(48, 75)` is a betrothed pair, since
`σ 1 48 = σ 1 75 = 124 = 48 + 75 + 1`. -/
lemma isBetrothedPair_48_75 : IsBetrothedPair 48 75 :=
  ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- Both members of a betrothed pair cannot be prime powers. -/
theorem not_both_primePower {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : IsBetrothedPair (p ^ a) (q ^ b)) : False := by
  obtain ⟨-, -, -, hEven⟩ := primePower_member_structure hp h
  obtain ⟨hqodd, -, -, -⟩ := primePower_member_structure hq h.symm
  exact (Nat.not_even_iff_odd.mpr hqodd.pow) hEven

#print axioms primePower_member_structure
#print axioms not_both_primePower
#print axioms isBetrothedPair_48_75

end Brockian.BetrothedNumbers

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

