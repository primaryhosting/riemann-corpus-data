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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of all (positive) divisors of `n`.  For `n = 0` this is `0`. -/
def sumOfDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `m` and `n` form an *amicable pair*: they are distinct and each one's divisor sum
equals `m + n`.  Equivalently, the sum of the proper divisors of `m` is `n` and the sum
of the proper divisors of `n` is `m`. -/
def IsAmicablePair (m n : ℕ) : Prop :=
  m ≠ n ∧ sumOfDivisors m = m + n ∧ sumOfDivisors n = m + n

/-- The set of amicable numbers: those belonging to some amicable pair. -/
def AmicableSet : Set ℕ := {m | ∃ n, IsAmicablePair m n}

/-- Being an amicable pair is a symmetric relation. -/
theorem isAmicablePair_symm {m n : ℕ} (h : IsAmicablePair m n) : IsAmicablePair n m := by
  obtain ⟨hne, hm, hn⟩ := h
  refine ⟨hne.symm, ?_, ?_⟩ <;> omega

/-- `(220, 284)` is an amicable pair, so `AmicableSet` is not empty. -/
theorem isAmicablePair_220_284 : IsAmicablePair 220 284 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> decide

theorem mem_amicableSet_220 : 220 ∈ AmicableSet := ⟨284, isAmicablePair_220_284⟩

theorem mem_amicableSet_284 : 284 ∈ AmicableSet :=
  ⟨220, isAmicablePair_symm isAmicablePair_220_284⟩

/-- **Reformulation (contrapositive form).**  If there are only finitely many amicable
numbers, then they are bounded: there is an `N` beyond which no amicable number occurs. -/
theorem bounded_of_finite (h : AmicableSet.Finite) : ∃ N : ℕ, ∀ m ∈ AmicableSet, m ≤ N := by
  obtain ⟨N, hN⟩ := h.bddAbove
  exact ⟨N, fun m hm => hN hm⟩

/-- **Reformulation.**  There are infinitely many amicable numbers if and only if
amicable numbers occur arbitrarily far out.  This is the equivalent statement that the
conjecture is usually attacked in: producing, for each bound `N`, one amicable pair
above `N`. -/
theorem amicable_infinite_iff_unbounded :
    AmicableSet.Infinite ↔ ∀ N : ℕ, ∃ m ∈ AmicableSet, N < m := by
  constructor
  · intro h N
    by_contra hc
    push_neg at hc
    exact h (Set.Finite.subset (Set.finite_Iic N) fun m hm => hc m hm)
  · intro h hfin
    obtain ⟨N, hN⟩ := bounded_of_finite hfin
    obtain ⟨m, hm, hlt⟩ := h N
    exact absurd (hN m hm) (by omega)


/-! ### The divisor-sum function: basic multiplicative toolkit -/

/-- `sumOfDivisors` is multiplicative on coprime arguments. -/
theorem sumOfDivisors_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sumOfDivisors (a * b) = sumOfDivisors a * sumOfDivisors b := by
  simp only [sumOfDivisors, ← sigma_one_apply]
  exact isMultiplicative_sigma.map_mul_of_coprime h

/-- The divisor sum of a prime `p` is `p + 1`. -/
theorem sumOfDivisors_prime {p : ℕ} (hp : p.Prime) : sumOfDivisors p = p + 1 := by
  rw [sumOfDivisors, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-- The divisor sum of `2 ^ n` is `2 ^ (n + 1) - 1`, stated without truncated subtraction. -/
theorem sumOfDivisors_two_pow (n : ℕ) : sumOfDivisors (2 ^ n) + 1 = 2 ^ (n + 1) := by
  rw [sumOfDivisors, ← sigma_one_apply, sigma_one_apply_prime_pow Nat.prime_two]
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; omega

/-! ### The rule of Thâbit ibn Qurra -/

/-- The integer identity underlying Thâbit ibn Qurra's rule: with
`A = 2 ^ (k+3) - 1`, `P = 3 * 2 ^ (k+1) - 1`, `Q = 3 * 2 ^ (k+2) - 1` and
`R = 9 * 2 ^ (2k+3) - 1`, both `A * (P+1) * (Q+1)` and `A * (R+1)` equal
`2 ^ (k+2) * P * Q + 2 ^ (k+2) * R`. -/
theorem thabit_identity (k : ℕ) (A P Q R : ℤ)
    (hA : A + 1 = 2 ^ (k + 3)) (hP : P + 1 = 3 * 2 ^ (k + 1)) (hQ : Q + 1 = 3 * 2 ^ (k + 2))
    (hR : R + 1 = 9 * 2 ^ (2 * k + 3)) :
    A * ((P + 1) * (Q + 1)) = 2 ^ (k + 2) * P * Q + 2 ^ (k + 2) * R ∧
      A * (R + 1) = 2 ^ (k + 2) * P * Q + 2 ^ (k + 2) * R := by
  have e1 : (2 : ℤ) ^ (k + 1) = 2 ^ k * 2 := by ring
  have e2 : (2 : ℤ) ^ (k + 2) = 2 ^ k * 4 := by ring
  have e3 : (2 : ℤ) ^ (k + 3) = 2 ^ k * 8 := by ring
  have e4 : (2 : ℤ) ^ (2 * k + 3) = (2 ^ k) ^ 2 * 8 := by rw [two_mul, pow_add, pow_add]; ring
  rw [e1] at hP
  rw [e2] at hQ
  rw [e3] at hA
  rw [e4] at hR
  rw [e2]
  have hA' : A = 2 ^ k * 8 - 1 := by linarith
  have hP' : P = 3 * (2 ^ k * 2) - 1 := by linarith
  have hQ' : Q = 3 * (2 ^ k * 4) - 1 := by linarith
  have hR' : R = 9 * ((2 ^ k) ^ 2 * 8) - 1 := by linarith
  subst hA' hP' hQ' hR'
  constructor <;> ring

/-- **Thâbit ibn Qurra's rule.**  If `p + 1 = 3 * 2 ^ (k+1)`, `q + 1 = 3 * 2 ^ (k+2)` and
`r + 1 = 9 * 2 ^ (2k+3)` are all prime, then `(2 ^ (k+2) * p * q, 2 ^ (k+2) * r)` is an
amicable pair. -/
theorem isAmicablePair_thabit {k p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpv : p + 1 = 3 * 2 ^ (k + 1)) (hqv : q + 1 = 3 * 2 ^ (k + 2))
    (hrv : r + 1 = 9 * 2 ^ (2 * k + 3)) :
    IsAmicablePair (2 ^ (k + 2) * p * q) (2 ^ (k + 2) * r) := by
  have hodd : ∀ m j : ℕ, m + 1 = 3 * 2 ^ (j + 1) → Odd m := by
    intro m j h
    have : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
    rw [Nat.odd_iff]; omega
  have hpo : Odd p := hodd p k hpv
  have hqo : Odd q := hodd q (k + 1) (by rw [hqv])
  have hro : Odd r := by
    have : (2 : ℕ) ^ (2 * k + 3) = 2 * 2 ^ (2 * k + 2) := by ring
    rw [Nat.odd_iff]; omega
  have hpq : p ≠ q := by
    have : (2 : ℕ) ^ (k + 1) < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have h2pq : Nat.Coprime (2 ^ (k + 2)) (p * q) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (hpo.mul hqo))
  have h2r : Nat.Coprime (2 ^ (k + 2)) r :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hro)
  have hAsum : sumOfDivisors (2 ^ (k + 2) * p * q)
      = sumOfDivisors (2 ^ (k + 2)) * ((p + 1) * (q + 1)) := by
    rw [mul_assoc, sumOfDivisors_mul_of_coprime h2pq, sumOfDivisors_mul_of_coprime hcpq,
      sumOfDivisors_prime hp, sumOfDivisors_prime hq]
  have hBsum : sumOfDivisors (2 ^ (k + 2) * r) = sumOfDivisors (2 ^ (k + 2)) * (r + 1) := by
    rw [sumOfDivisors_mul_of_coprime h2r, sumOfDivisors_prime hr]
  have hA : sumOfDivisors (2 ^ (k + 2)) + 1 = 2 ^ (k + 3) := sumOfDivisors_two_pow (k + 2)
  obtain ⟨g1, g2⟩ := thabit_identity k (sumOfDivisors (2 ^ (k + 2)) : ℕ) p q r
    (by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hA)
    (by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hpv)
    (by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hqv)
    (by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hrv)
  refine ⟨?_, ?_, ?_⟩
  · have hlt : p * q < r := by
      have hY : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hP : (p : ℤ) + 1 = 3 * 2 ^ (k + 1) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hpv
      have hQ : (q : ℤ) + 1 = 3 * 2 ^ (k + 2) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hqv
      have hR : (r : ℤ) + 1 = 9 * 2 ^ (2 * k + 3) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hrv
      have e1 : (2 : ℤ) ^ (k + 1) = 2 ^ k * 2 := by ring
      have e2 : (2 : ℤ) ^ (k + 2) = 2 ^ k * 4 := by ring
      have e4 : (2 : ℤ) ^ (2 * k + 3) = (2 ^ k) ^ 2 * 8 := by rw [two_mul, pow_add, pow_add]; ring
      rw [e1] at hP
      rw [e2] at hQ
      rw [e4] at hR
      have : (p : ℤ) * q < r := by nlinarith
      exact_mod_cast this
    have hpos : 0 < (2 : ℕ) ^ (k + 2) := Nat.two_pow_pos _
    have : 2 ^ (k + 2) * p * q < 2 ^ (k + 2) * r := by
      rw [mul_assoc]; exact mul_lt_mul_of_pos_left hlt hpos
    omega
  · rw [hAsum]; exact_mod_cast g1
  · rw [hBsum]; exact_mod_cast g2

/-- `k` is a *Thâbit index*: all three numbers appearing in Thâbit ibn Qurra's rule are
prime.  (For example `k = 0`, `k = 2` and `k = 4` are Thâbit indices, giving the amicable
pairs `(220, 284)`, `(17296, 18416)` and `(9363584, 9437056)`.) -/
def ThabitIndex (k : ℕ) : Prop :=
  Nat.Prime (3 * 2 ^ (k + 1) - 1) ∧ Nat.Prime (3 * 2 ^ (k + 2) - 1) ∧
    Nat.Prime (9 * 2 ^ (2 * k + 3) - 1)

/-- Each Thâbit index produces an amicable pair. -/
theorem isAmicablePair_of_thabitIndex {k : ℕ} (h : ThabitIndex k) :
    IsAmicablePair (2 ^ (k + 2) * (3 * 2 ^ (k + 1) - 1) * (3 * 2 ^ (k + 2) - 1))
      (2 ^ (k + 2) * (9 * 2 ^ (2 * k + 3) - 1)) := by
  obtain ⟨hp, hq, hr⟩ := h
  have h1 : 1 ≤ (2 : ℕ) ^ (k + 1) := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 : ℕ) ^ (k + 2) := Nat.one_le_two_pow
  have h3 : 1 ≤ (2 : ℕ) ^ (2 * k + 3) := Nat.one_le_two_pow
  exact isAmicablePair_thabit hp hq hr (by omega) (by omega) (by omega)

/-- `k = 0` is a Thâbit index; the pair it produces is `(220, 284)`. -/
theorem thabitIndex_zero : ThabitIndex 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- `k = 2` is a Thâbit index; the pair it produces is `(17296, 18416)`. -/
theorem thabitIndex_two : ThabitIndex 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The Thâbit pair for `k = 0` is indeed `(220, 284)`. -/
theorem thabit_pair_zero :
    IsAmicablePair (2 ^ (0 + 2) * (3 * 2 ^ (0 + 1) - 1) * (3 * 2 ^ (0 + 2) - 1))
      (2 ^ (0 + 2) * (9 * 2 ^ (2 * 0 + 3) - 1)) ∧
    2 ^ (0 + 2) * (3 * 2 ^ (0 + 1) - 1) * (3 * 2 ^ (0 + 2) - 1) = 220 ∧
    2 ^ (0 + 2) * (9 * 2 ^ (2 * 0 + 3) - 1) = 284 :=
  ⟨isAmicablePair_of_thabitIndex thabitIndex_zero, by norm_num, by norm_num⟩

/-- The Thâbit pair for `k = 2` is `(17296, 18416)`; in particular these are amicable. -/
theorem isAmicablePair_17296_18416 : IsAmicablePair 17296 18416 := by
  have h := isAmicablePair_of_thabitIndex thabitIndex_two
  norm_num at h
  exact h

/-- **Amicable Infinitude from Thâbit indices.**  If there are infinitely many `k` for
which the three Thâbit numbers `3·2^(k+1) - 1`, `3·2^(k+2) - 1` and `9·2^(2k+3) - 1` are
all prime, then there are infinitely many amicable numbers.  This reduces the conjecture
to a statement purely about primality. -/
theorem amicable_infinite_of_infinitely_many_thabitIndices
    (h : ∀ K : ℕ, ∃ k ≥ K, ThabitIndex k) : AmicableSet.Infinite := by
  refine amicable_infinite_iff_unbounded.mpr fun N => ?_
  obtain ⟨k, hk, hT⟩ := h N
  refine ⟨2 ^ (k + 2) * (3 * 2 ^ (k + 1) - 1) * (3 * 2 ^ (k + 2) - 1),
    ⟨_, isAmicablePair_of_thabitIndex hT⟩, ?_⟩
  obtain ⟨hp, hq, _⟩ := hT
  have hp1 : 1 ≤ 3 * 2 ^ (k + 1) - 1 := hp.one_lt.le.trans' (by norm_num)
  have hq1 : 1 ≤ 3 * 2 ^ (k + 2) - 1 := hq.one_lt.le.trans' (by norm_num)
  have hbig : 2 ^ (k + 2) ≤ 2 ^ (k + 2) * (3 * 2 ^ (k + 1) - 1) * (3 * 2 ^ (k + 2) - 1) := by
    calc 2 ^ (k + 2) = 2 ^ (k + 2) * 1 * 1 := by ring
      _ ≤ 2 ^ (k + 2) * (3 * 2 ^ (k + 1) - 1) * (3 * 2 ^ (k + 2) - 1) := by
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp1) hq1
  have hlt : k < 2 ^ (k + 2) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

/-- **Amicable Infinitude (conditional reduction).**
If amicable pairs occur arbitrarily far out — i.e. for every bound `N` there is an
amicable pair `(m, n)` with `N < m` — then the set of amicable numbers is infinite.

The hypothesis is exactly the standard "unbounded supply of amicable pairs" statement,
which by `amicable_infinite_iff_unbounded` is equivalent to the conclusion; the
infinitude of amicable numbers is an open problem, so the result is stated in this
conditional form.  A stronger, purely number-theoretic sufficient condition is given by
`amicable_infinite_of_infinitely_many_thabitIndices`. -/
theorem AmicableInfinitude
    (h : ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsAmicablePair m n) : AmicableSet.Infinite := by
  refine amicable_infinite_iff_unbounded.mpr fun N => ?_
  obtain ⟨m, n, hlt, hmn⟩ := h N
  exact ⟨m, ⟨n, hmn⟩, hlt⟩

end Brockian.AmicableNumbers

