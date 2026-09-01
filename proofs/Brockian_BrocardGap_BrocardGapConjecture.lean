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

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

/-- The number of primes strictly between `a` and `b`. -/
def primeCountIn (a b : ℕ) : ℕ := ((Finset.Ioo a b).filter Nat.Prime).card

/-- **Oppermann's conjecture**: for every `x > 1` there is a prime strictly between
`x² - x` and `x²`, and a prime strictly between `x²` and `x² + x`. -/
def Oppermann : Prop :=
  ∀ x : ℕ, 1 < x →
    (∃ p : ℕ, p.Prime ∧ x * x - x < p ∧ p < x * x) ∧
    (∃ p : ℕ, p.Prime ∧ x * x < p ∧ p < x * x + x)

/-- Under Oppermann's conjecture, for any `P ≥ 3` and any `q ≥ P + 2` there are at least
four primes strictly between `P²` and `q²`. -/
theorem four_primes_of_oppermann (hO : Oppermann) (P q : ℕ) (hP : 3 ≤ P) (hq : P + 2 ≤ q) :
    4 ≤ primeCountIn (P ^ 2) (q ^ 2) := by
  obtain ⟨-, a, ha, ha1, ha2⟩ := hO P (by omega)
  obtain ⟨⟨b, hb, hb1, hb2⟩, c, hc, hc1, hc2⟩ := hO (P + 1) (by omega)
  obtain ⟨⟨d, hd, hd1, hd2⟩, -⟩ := hO (P + 2) (by omega)
  have e1 : (P + 1) * (P + 1) = P * P + 2 * P + 1 := by ring
  have e2 : (P + 2) * (P + 2) = P * P + 4 * P + 4 := by ring
  rw [e1] at hb1 hb2 hc1 hc2
  rw [e2] at hd1 hd2
  have hqq : P * P + 4 * P + 4 ≤ q * q := by
    rw [← e2]; exact Nat.mul_le_mul hq hq
  have hp2 : P ^ 2 = P * P := sq P
  have hq2 : q ^ 2 = q * q := sq q
  set S := P * P with hS
  set T := q * q with hT
  clear_value S T
  have hsub : ({a, b, c, d} : Finset ℕ) ⊆ (Finset.Ioo (P ^ 2) (q ^ 2)).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨⟨by omega, by omega⟩, ha⟩
    · exact ⟨⟨by omega, by omega⟩, hb⟩
    · exact ⟨⟨by omega, by omega⟩, hc⟩
    · exact ⟨⟨by omega, by omega⟩, hd⟩
  have hcard : ({a, b, c, d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  calc (4 : ℕ) = ({a, b, c, d} : Finset ℕ).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The second prime is `3`. -/
theorem nth_prime_one : Nat.nth Nat.Prime 1 = 3 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  rwa [show Nat.count Nat.Prime 3 = 1 from by decide] at h

theorem three_le_nth_prime {n : ℕ} (hn : 1 ≤ n) : 3 ≤ Nat.nth Nat.Prime n := by
  rw [← nth_prime_one]
  exact Nat.nth_monotone Nat.infinite_setOf_prime hn

/-- Consecutive primes from `3` on differ by at least `2`. -/
theorem succ_nth_prime_ge {n : ℕ} (hn : 1 ≤ n) :
    Nat.nth Nat.Prime n + 2 ≤ Nat.nth Nat.Prime (n + 1) := by
  have h3 : 3 ≤ Nat.nth Nat.Prime n := three_le_nth_prime hn
  have hlt : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (Nat.lt_succ_self n)
  have hodd : Odd (Nat.nth Nat.Prime n) :=
    (Nat.prime_nth_prime n).odd_of_ne_two (by omega)
  have hodd' : Odd (Nat.nth Nat.Prime (n + 1)) :=
    (Nat.prime_nth_prime (n + 1)).odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨l, hl⟩ := hodd'
  omega

/-- **Brocard's gap conjecture**, conditional on Oppermann's conjecture: for `n ≥ 1`
(i.e. from the prime `3` on) there are at least four primes strictly between the squares
of two consecutive primes `p_n` and `p_{n+1}`. -/
theorem BrocardGapConjecture (hO : Oppermann) (n : ℕ) (hn : 1 ≤ n) :
    4 ≤ primeCountIn ((Nat.nth Nat.Prime n) ^ 2) ((Nat.nth Nat.Prime (n + 1)) ^ 2) :=
  four_primes_of_oppermann hO _ _ (three_le_nth_prime hn) (succ_nth_prime_ge hn)

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- Unconditional verification of the Brocard gap bound for the first six consecutive prime
pairs `(p, q)` starting from `(3, 5)`: there are at least four primes strictly between `p²`
and `q²`. -/
theorem brocardGap_small_cases :
    ∀ pq ∈ [(3, 5), (5, 7), (7, 11), (11, 13), (13, 17), (17, 19)],
      4 ≤ primeCountIn (pq.1 ^ 2) (pq.2 ^ 2) := by decide

end Brockian.BrocardGap

