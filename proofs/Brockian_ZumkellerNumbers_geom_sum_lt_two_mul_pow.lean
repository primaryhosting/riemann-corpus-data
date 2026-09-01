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

namespace Brockian.ZumkellerNumbers

def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

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

end Brockian.ZumkellerNumbers

