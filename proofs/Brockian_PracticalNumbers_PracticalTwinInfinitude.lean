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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace PracticalNumbers

/-- A natural number `n` is *practical* if it is positive and every `t ≤ n` can be written
as a sum of *distinct* divisors of `n` (the standard definition, cf. OEIS A005153). -/
def Practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ t ≤ n, ∃ S ⊆ n.divisors, ∑ d ∈ S, d = t

theorem practical_one : Practical 1 := by
  refine ⟨one_pos, ?_⟩
  intro t ht
  interval_cases t
  · exact ⟨∅, by simp⟩
  · exact ⟨{1}, by simp⟩

/-- Key closure lemma (a weak form of Stewart's lemma): if `n` is practical and
`1 ≤ m ≤ n + 1`, then `n * m` is practical. -/
theorem practical_mul {n m : ℕ} (hn : Practical n) (hm : 0 < m) (hmn : m ≤ n + 1) :
    Practical (n * m) := by
  obtain ⟨hn0, hn⟩ := hn
  refine ⟨Nat.mul_pos hn0 hm, ?_⟩
  intro t ht
  have hq : t / m ≤ n := by
    calc t / m ≤ (n * m) / m := Nat.div_le_div_right ht
    _ = n := Nat.mul_div_cancel _ hm
  have hrlt : t % m < m := Nat.mod_lt _ hm
  have hr : t % m ≤ n := by omega
  obtain ⟨Sq, hSq, hsq⟩ := hn _ hq
  obtain ⟨Sr, hSr, hsr⟩ := hn _ hr
  have hSrle : ∀ y ∈ Sr, y ≤ t % m := by
    intro y hy
    rw [← hsr]
    exact Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) hy
  refine ⟨(Sq.image (fun d => m * d)) ∪ Sr, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_image] at hx
    rcases hx with ⟨d, hd, rfl⟩ | hx
    · have hdd := (Nat.mem_divisors.1 (hSq hd)).1
      rw [Nat.mem_divisors]
      refine ⟨?_, by positivity⟩
      have h := mul_dvd_mul_left m hdd
      rwa [Nat.mul_comm m n] at h
    · have hdd := (Nat.mem_divisors.1 (hSr hx)).1
      rw [Nat.mem_divisors]
      exact ⟨hdd.trans (Dvd.intro m rfl), by positivity⟩
  · have hdisj : Disjoint (Sq.image (fun d => m * d)) Sr := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      simp only [Finset.mem_image] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (hSq hd)
      have h2 := hSrle _ hx2
      nlinarith [hrlt]
    rw [Finset.sum_union hdisj,
      Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h),
      ← Finset.mul_sum, hsq, hsr]
    exact Nat.div_add_mod t m

theorem practical_two : Practical 2 := by
  have := practical_mul practical_one (m := 2) (by norm_num) (by norm_num)
  simpa using this

/-- Every number of the form `2 * 3 ^ j` is practical. -/
theorem practical_two_mul_three_pow (j : ℕ) : Practical (2 * 3 ^ j) := by
  induction j with
  | zero => simpa using practical_two
  | succ j ih =>
      have hpos : 0 < 2 * 3 ^ j := by positivity
      have h := practical_mul ih (m := 3) (by norm_num) (by omega)
      have he : 2 * 3 ^ j * 3 = 2 * 3 ^ (j + 1) := by ring
      rwa [he] at h

/-- Two less than `2 * 3 ^ (2 ^ k)` is practical, for every `k`. -/
theorem practical_two_mul_three_pow_two_pow_sub_two (k : ℕ) :
    Practical (2 * 3 ^ (2 ^ k) - 2) := by
  induction k with
  | zero =>
      have h := practical_mul practical_two (m := 2) (by norm_num) (by norm_num)
      norm_num at h ⊢
      exact h
  | succ k ih =>
      set m : ℕ := 3 ^ (2 ^ k) with hm
      have hm2 : 2 ≤ m := by
        have : 3 ^ 1 ≤ 3 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
        omega
      have hstep : 2 * 3 ^ (2 ^ (k + 1)) - 2 = (2 * m - 2) * (m + 1) := by
        have hsq : 3 ^ (2 ^ (k + 1)) = m * m := by
          rw [hm, ← pow_add]
          congr 1
          ring
        rw [hsq]
        obtain ⟨j, hj⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
        have hexp : 2 * ((j + 2) * (j + 2)) = (2 * (j + 2) - 2) * ((j + 2) + 1) + 2 := by
          have h2 : 2 * (j + 2) - 2 = 2 * j + 2 := by omega
          rw [h2]; ring
        rw [hj]
        omega
      rw [hstep]
      refine practical_mul ih (by omega) ?_
      omega

/-- **Practical twin infinitude**: the set of `n` such that both `n` and `n + 2` are
practical numbers is infinite. -/
theorem PracticalTwinInfinitude : {n : ℕ | Practical n ∧ Practical (n + 2)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨2 * 3 ^ (2 ^ a) - 2, ⟨practical_two_mul_three_pow_two_pow_sub_two a, ?_⟩, ?_⟩
  · have hm2 : 2 ≤ 3 ^ (2 ^ a) := by
      have : 3 ^ 1 ≤ 3 ^ (2 ^ a) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
      omega
    have he : 2 * 3 ^ (2 ^ a) - 2 + 2 = 2 * 3 ^ (2 ^ a) := by omega
    rw [he]
    exact practical_two_mul_three_pow _
  · have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2 : 2 ^ a ≤ 2 ^ (2 ^ a) := Nat.pow_le_pow_right (by norm_num) h1.le
    have h3 : 2 ^ (2 ^ a) ≤ 3 ^ (2 ^ a) := Nat.pow_le_pow_left (by norm_num) _
    have h4 : 2 ^ 1 ≤ 2 ^ (2 ^ a) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    omega

end PracticalNumbers
end Brockian

