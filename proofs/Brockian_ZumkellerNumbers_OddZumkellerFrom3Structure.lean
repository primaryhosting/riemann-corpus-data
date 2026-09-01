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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ZumkellerNumbers

open Finset

/-- A natural number `n` is a *Zumkeller number* if it is positive and its set of divisors
can be split into two parts of equal sum; equivalently, some set `S` of divisors of `n`
satisfies `2 * ∑ S = σ₁ n`. -/
def Zumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, 2 * ∑ d ∈ S, d = ∑ d ∈ n.divisors, d

/-- The map `(a, b) ↦ a * b` is injective on pairs of divisors of two coprime numbers. -/
lemma injOn_mul_divisors {m n : ℕ} (hcop : m.Coprime n) (S : Finset ℕ) (hS : S ⊆ m.divisors) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ((S ×ˢ n.divisors : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
  simp only [Finset.mem_coe, Finset.mem_product] at hab hcd
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨hc, hd⟩ := hcd
  have ham : a ∣ m := (Nat.mem_divisors.1 (hS ha)).1
  have hcm : c ∣ m := (Nat.mem_divisors.1 (hS hc)).1
  have hbn : b ∣ n := (Nat.mem_divisors.1 hb).1
  have hdn : d ∣ n := (Nat.mem_divisors.1 hd).1
  have hapos : 0 < a := Nat.pos_of_mem_divisors (hS ha)
  have had : a.Coprime d :=
    Nat.Coprime.coprime_dvd_left ham (Nat.Coprime.coprime_dvd_right hdn hcop)
  have hcb : c.Coprime b :=
    Nat.Coprime.coprime_dvd_left hcm (Nat.Coprime.coprime_dvd_right hbn hcop)
  simp only at h
  have h1 : a ∣ c := had.dvd_of_dvd_mul_right (h ▸ Dvd.intro b rfl)
  have h2 : c ∣ a := hcb.dvd_of_dvd_mul_right (h ▸ Dvd.intro d rfl)
  have hac : a = c := Nat.dvd_antisymm h1 h2
  subst hac
  have hbd : b = d := Nat.eq_of_mul_eq_mul_left hapos h
  simp [hbd]

/-- If `m` is Zumkeller and `n` is a positive number coprime to `m`, then `m * n` is Zumkeller. -/
theorem Zumkeller.mul_coprime {m n : ℕ} (hm : Zumkeller m) (hn : 0 < n) (hcop : m.Coprime n) :
    Zumkeller (m * n) := by
  obtain ⟨hmpos, S, hS, hsum⟩ := hm
  classical
  refine ⟨Nat.mul_pos hmpos hn, (S ×ˢ n.divisors).image (fun p : ℕ × ℕ => p.1 * p.2), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_product] at hx
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hx
    have ham : a ∣ m := (Nat.mem_divisors.1 (hS ha)).1
    have hbn : b ∣ n := (Nat.mem_divisors.1 hb).1
    exact Nat.mem_divisors.2 ⟨mul_dvd_mul ham hbn, Nat.mul_ne_zero hmpos.ne' hn.ne'⟩
  · rw [Finset.sum_image (injOn_mul_divisors hcop S hS), Finset.sum_product]
    have hprod : ∑ a ∈ S, ∑ b ∈ n.divisors, a * b
        = (∑ a ∈ S, a) * (∑ b ∈ n.divisors, b) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    rw [hprod, ← mul_assoc, hsum, hcop.sum_divisors_mul]

set_option maxRecDepth 100000 in
/-- The sum of the divisors of `945 = 3^3 · 5 · 7` is `1920`. -/
lemma sum_divisors_945 : ∑ d ∈ (945 : ℕ).divisors, d = 1920 := by rfl

/-- `945 = 3^3 · 5 · 7`, the smallest odd Zumkeller number, is indeed Zumkeller:
the divisors `{15, 945}` sum to `960 = 1920 / 2`. -/
theorem zumkeller_945 : Zumkeller 945 := by
  refine ⟨by norm_num, {15, 945}, ?_, ?_⟩
  · intro x hx
    fin_cases hx <;> exact Nat.mem_divisors.2 (by norm_num)
  · rw [sum_divisors_945]
    norm_num

/-- **Odd Zumkeller numbers from the `3`-structure of `945`.**

For every odd `n` coprime to `945 = 3^3 · 5 · 7`, the number `945 * n` is an odd
Zumkeller number divisible by `27 = 3^3`. -/
theorem OddZumkellerFrom3Structure (n : ℕ) (hodd : Odd n) (hcop : Nat.Coprime 945 n) :
    Odd (945 * n) ∧ 27 ∣ (945 * n) ∧ Zumkeller (945 * n) :=
  ⟨(by norm_num : Odd (945 : ℕ)).mul hodd,
   Dvd.dvd.mul_right (by norm_num) n,
   zumkeller_945.mul_coprime hodd.pos hcop⟩

/-- Consequently there are infinitely many odd Zumkeller numbers divisible by `27`. -/
theorem infinite_odd_zumkeller :
    {n : ℕ | Odd n ∧ 27 ∣ n ∧ Zumkeller n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (a + 946)
  have hp945 : ¬ (p ∣ 945) := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hcop : Nat.Coprime 945 p := (Nat.Prime.coprime_iff_not_dvd hpp |>.2 hp945).symm
  have hodd : Odd p := hpp.odd_of_ne_two (by omega)
  refine ⟨945 * p, OddZumkellerFrom3Structure p hodd hcop, ?_⟩
  nlinarith [hp]

end Brockian.ZumkellerNumbers

