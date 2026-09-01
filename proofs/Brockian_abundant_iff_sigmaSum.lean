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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Status of the target

`Brockian.WeirdNumbers.OddWeirdExists` states that some odd weird number exists
(weird = abundant but not pseudoperfect, in Mathlib's `Nat.Weird`). Whether an odd
weird number exists is an open problem, so it is stated here as a `Prop`-valued
definition and *not* asserted. What is proved unconditionally in this file is:

* `isWeird_mul_prime` : if `n` is weird and `p` is a prime exceeding the sum of the
  divisors of `n`, then `n * p` is weird;
* `oddWeirdExists_iff_infinite` : `OddWeirdExists` holds iff there are infinitely many
  odd weird numbers (a conditional reduction obtained from `isWeird_mul_prime`);
* `weird_seventy` : `70` is weird, so weird numbers do exist;
* `not_weird_of_odd_lt_946` : no odd number below `946` is weird, hence
  `oddWeird_ge_946` : any witness for `OddWeirdExists` is at least `946`.

Mathlib supplies the basic vocabulary (`Nat.Abundant`, `Nat.Pseudoperfect`, `Nat.Weird`
and `Nat.abundant_iff_sum_divisors` in `Mathlib/NumberTheory/FactorisationProperties.lean`,
all of which are used below), but no lemma there closes or nearly closes the target:
`exact?`/`apply?` find nothing, and Mathlib proves no existence results about weird
numbers at all, so everything below is developed from scratch.
-/

open Finset

namespace Brockian
namespace WeirdNumbers

/-- The sum of all (positive) divisors of `n`. -/
def sigmaSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- The statement "an odd weird number exists" (an open problem).
Here `Nat.Weird n` means that `n` is abundant but not pseudoperfect, i.e. no set of
proper divisors of `n` sums to `n`. -/
def OddWeirdExists : Prop := ∃ n : ℕ, Odd n ∧ n.Weird

lemma abundant_iff_sigmaSum {n : ℕ} : n.Abundant ↔ 2 * n < sigmaSum n :=
  Nat.abundant_iff_sum_divisors

lemma self_le_sigmaSum {n : ℕ} (hn : n ≠ 0) : n ≤ sigmaSum n :=
  Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self n hn)

lemma weird_ne_zero {n : ℕ} (hw : n.Weird) : n ≠ 0 := by
  rintro rfl
  exact Nat.not_abundant_zero hw.1

/-! ### Divisors of `n * p` for a prime `p` -/

lemma divisors_mul_prime {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    (n * p).divisors = n.divisors ∪ n.divisors.image (fun d => p * d) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  ext d
  simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨hd, -⟩
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      right
      refine ⟨e, ⟨?_, hn⟩, rfl⟩
      have hpe : p * e ∣ p * n := by
        rw [mul_comm n p] at hd; exact hd
      exact (mul_dvd_mul_iff_left hp0).mp hpe
    · left
      refine ⟨?_, hn⟩
      have hcop : Nat.Coprime d p :=
        Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
      exact hcop.dvd_of_dvd_mul_right hd
  · rintro (⟨hd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
    · exact ⟨hd.mul_right p, by positivity⟩
    · refine ⟨?_, by positivity⟩
      rw [mul_comm n p]
      exact mul_dvd_mul_left p he

lemma disjoint_divisors_image {n p : ℕ} (hpn : ¬ p ∣ n) :
    Disjoint n.divisors (n.divisors.image (fun d => p * d)) := by
  rw [Finset.disjoint_right]
  rintro a ha hb
  simp only [Finset.mem_image, Nat.mem_divisors] at ha hb
  obtain ⟨e, -, rfl⟩ := ha
  exact hpn (dvd_trans (Dvd.intro e rfl) hb.1)

lemma sigmaSum_mul_prime {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : ¬ p ∣ n) :
    sigmaSum (n * p) = sigmaSum n * (1 + p) := by
  have hinj : Set.InjOn (fun d => p * d) (n.divisors : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp.pos hab
  unfold sigmaSum
  rw [divisors_mul_prime hn hp, Finset.sum_union (disjoint_divisors_image hpn),
    Finset.sum_image hinj, ← Finset.mul_sum]
  ring

/-! ### Multiplying a weird number by a large prime keeps it weird -/

/-- If `n` is weird and `p` is a prime larger than the sum of the divisors of `n`,
then `n * p` is weird. -/
theorem isWeird_mul_prime {n p : ℕ} (hp : p.Prime) (hlt : sigmaSum n < p) (hw : n.Weird) :
    (n * p).Weird := by
  have hn : n ≠ 0 := weird_ne_zero hw
  have hnle : n ≤ sigmaSum n := self_le_sigmaSum hn
  have hpn : ¬ p ∣ n := by
    intro hdvd
    have hpn' : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    omega
  obtain ⟨habund, hpseudo⟩ := hw
  rw [abundant_iff_sigmaSum] at habund
  constructor
  · rw [abundant_iff_sigmaSum, sigmaSum_mul_prime hn hp hpn]
    have hp1 : 1 ≤ p := hp.one_lt.le
    nlinarith [habund, hp1]
  · rintro ⟨-, S, hS, hsum⟩
    have hSsub : S ⊆ (n * p).divisors := hS.trans Nat.properDivisors_subset_divisors
    classical
    set A : Finset ℕ := S.filter (fun d => ¬ p ∣ d) with hA
    set B : Finset ℕ := S.filter (fun d => p ∣ d) with hB
    have hAB : A ∪ B = S := by
      ext x
      simp only [hA, hB, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        by_cases h : p ∣ x
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl ⟨hx, h⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [hA, hB, Finset.mem_filter] at ha hb
      exact ha.2 hb.2
    have hsumsplit : ∑ d ∈ A, d + ∑ d ∈ B, d = n * p := by
      rw [← Finset.sum_union hdisj, hAB, hsum]
    have hAdvd : A ⊆ n.divisors := by
      intro a ha
      simp only [hA, Finset.mem_filter] at ha
      have hmem := hSsub ha.1
      rw [divisors_mul_prime hn hp] at hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact h
      · exfalso
        simp only [Finset.mem_image] at h
        obtain ⟨e, -, rfl⟩ := h
        exact ha.2 (Dvd.intro e rfl)
    have hBsub : B ⊆ n.divisors.image (fun d => p * d) := by
      intro a ha
      simp only [hB, Finset.mem_filter] at ha
      have hmem := hSsub ha.1
      rw [divisors_mul_prime hn hp] at hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact absurd (dvd_trans ha.2 (Nat.mem_divisors.mp h).1) hpn
      · exact h
    obtain ⟨C, hC, hCimage⟩ := Finset.subset_image_iff.mp hBsub
    have hinj : Set.InjOn (fun d => p * d) (C : Set ℕ) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos hab
    have hBsum : ∑ d ∈ B, d = p * ∑ d ∈ C, d := by
      rw [← hCimage, Finset.sum_image hinj, Finset.mul_sum]
    have hAle : ∑ d ∈ A, d ≤ sigmaSum n := by
      unfold sigmaSum
      exact Finset.sum_le_sum_of_subset hAdvd
    have hAdvdp : p ∣ ∑ d ∈ A, d := by
      have hcomm : n * p = p * n := mul_comm n p
      refine ⟨n - ∑ d ∈ C, d, ?_⟩
      rw [Nat.mul_sub]
      omega
    have hA0 : ∑ d ∈ A, d = 0 := by
      rcases Nat.eq_zero_or_pos (∑ d ∈ A, d) with h | h
      · exact h
      · have := Nat.le_of_dvd h hAdvdp
        omega
    have hCsum : ∑ d ∈ C, d = n := by
      have hmul : p * ∑ d ∈ C, d = p * n := by
        rw [mul_comm p n]; omega
      exact Nat.eq_of_mul_eq_mul_left hp.pos hmul
    have hCproper : C ⊆ n.properDivisors := by
      intro c hc
      have hcn : c ∣ n := (Nat.mem_divisors.mp (hC hc)).1
      rw [Nat.mem_properDivisors]
      refine ⟨hcn, ?_⟩
      rcases lt_or_ge c n with h | h
      · exact h
      · exfalso
        have hcn' : c = n := le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hcn) h
        subst hcn'
        have hmem : p * c ∈ B := by
          rw [← hCimage]
          exact Finset.mem_image_of_mem _ hc
        have hmemS : p * c ∈ S := (Finset.mem_filter.mp hmem).1
        have hprop := hS hmemS
        rw [Nat.mem_properDivisors] at hprop
        have hcomm : p * c = c * p := mul_comm p c
        omega
    exact hpseudo ⟨Nat.pos_of_ne_zero hn, C, hCproper, hCsum⟩

/-! ### Consequence: one odd weird number yields arbitrarily large ones -/

/-- If an odd weird number exists, then there are arbitrarily large odd weird numbers. -/
theorem oddWeird_unbounded_of_oddWeirdExists (h : OddWeirdExists) (N : ℕ) :
    ∃ m : ℕ, N < m ∧ Odd m ∧ m.Weird := by
  obtain ⟨n, hodd, hw⟩ := h
  have hn : n ≠ 0 := weird_ne_zero hw
  have habund : 2 * n < sigmaSum n := abundant_iff_sigmaSum.mp hw.1
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max (sigmaSum n + 1) (N + 1))
  have hlt : sigmaSum n < p := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) hpge)
  have hNp : N < p := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right _ _) hpge)
  refine ⟨n * p, ?_, ?_, isWeird_mul_prime hp hlt hw⟩
  · calc N < p := hNp
      _ = 1 * p := (one_mul p).symm
      _ ≤ n * p := Nat.mul_le_mul_right p (Nat.one_le_iff_ne_zero.mpr hn)
  · have hpodd : Odd p := by
      rcases hp.eq_two_or_odd' with rfl | hodd'
      · exact absurd hlt (by omega)
      · exact hodd'
    exact hodd.mul hpodd

/-- Hence the existence of an odd weird number is equivalent to the existence of
infinitely many of them. -/
theorem oddWeirdExists_iff_infinite :
    OddWeirdExists ↔ {n : ℕ | Odd n ∧ n.Weird}.Infinite := by
  constructor
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨m, hm, hodd, hw⟩ := oddWeird_unbounded_of_oddWeirdExists h N
    exact absurd (hN ⟨hodd, hw⟩) (not_le.mpr hm)
  · intro h
    obtain ⟨n, hn⟩ := h.nonempty
    exact ⟨n, hn.1, hn.2⟩

/-! ### Weird numbers do exist: `70` is weird -/

set_option maxRecDepth 100000 in
theorem weird_seventy : Nat.Weird 70 := by decide

theorem weirdExists : ∃ n : ℕ, n.Weird := ⟨70, weird_seventy⟩

/-! ### A verified partial result towards `OddWeirdExists`: no small odd weird number -/

set_option maxRecDepth 100000 in
/-- `945`, the smallest odd abundant number, is pseudoperfect (hence not weird):
`945 = 1+5+7+9+15+21+35+45+63+105+135+189+315`. -/
theorem pseudoperfect_945 : Nat.Pseudoperfect 945 :=
  ⟨by norm_num, {1, 5, 7, 9, 15, 21, 35, 45, 63, 105, 135, 189, 315}, by decide, by decide⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
private theorem no_odd_weird_lt_945 : ∀ n ∈ Finset.range 945, Odd n → ¬ n.Weird := by
  decide

/-- No odd number below `946` is weird; in particular any witness for `OddWeirdExists`
must exceed `945`. -/
theorem not_weird_of_odd_lt_946 {n : ℕ} (hn : n < 946) (hodd : Odd n) : ¬ n.Weird := by
  intro hw
  by_cases h : n = 945
  · exact hw.2 (h ▸ pseudoperfect_945)
  · exact no_odd_weird_lt_945 n (Finset.mem_range.mpr (by omega)) hodd hw

/-- Consequently, if an odd weird number exists, it is at least `946`. -/
theorem oddWeird_ge_946 (h : OddWeirdExists) :
    ∃ n : ℕ, 946 ≤ n ∧ Odd n ∧ n.Weird := by
  obtain ⟨n, hodd, hw⟩ := h
  refine ⟨n, ?_, hodd, hw⟩
  by_contra hlt
  exact not_weird_of_odd_lt_946 (by omega) hodd hw

end WeirdNumbers
end Brockian

