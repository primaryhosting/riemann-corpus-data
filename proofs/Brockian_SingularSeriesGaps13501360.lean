/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of Hardy–Littlewood, i.e. the
singular series `𝔖(H)` is nonzero) when for every prime `p` some residue class mod `p`
contains no element of `H`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℤ, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (h - r))

/-- For an odd prime `p`, a two–element set `{0, n}` always misses a residue class:
one of the classes `1` or `2` is missed. -/
lemma pair_odd_prime (n : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ r : ℤ, ∀ h ∈ ({0, n} : Finset ℤ), ¬ ((p : ℤ) ∣ (h - r)) := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p; simp_all
    · exact h
  have hp3' : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  -- either `1` or `2` works
  by_cases h1 : (p : ℤ) ∣ (n - 1)
  · refine ⟨2, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · intro hd
      have : (p : ℤ) ∣ 2 := by simpa using hd.neg_right
      have := Int.le_of_dvd (by norm_num) this
      omega
    · intro hd
      have hdd : (p : ℤ) ∣ ((h - 1) - (h - 2)) := h1.sub hd
      simp at hdd
      have := Int.le_of_dvd (by norm_num) hdd
      omega
  · refine ⟨1, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · intro hd
      have : (p : ℤ) ∣ 1 := by simpa using hd.neg_right
      have := Int.le_of_dvd (by norm_num) this
      omega
    · exact h1

/-- A pair `{0, n}` is admissible exactly when the gap `n` is even. -/
theorem admissible_pair_iff (n : ℤ) : Admissible ({0, n} : Finset ℤ) ↔ Even n := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h 2 Nat.prime_two
    have h0 := hr 0 (by simp)
    have hn := hr n (by simp)
    simp only [Nat.cast_ofNat, zero_sub] at h0 hn
    rw [Int.even_iff]
    omega
  · intro hn p hp
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨1, ?_⟩
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      obtain ⟨m, hm⟩ := hn
      rcases hh with rfl | rfl <;> intro hd <;> simp at hd
      omega
    · exact pair_odd_prime n p hp hp2

/-- The admissible gaps in the range `[1350, 1360]`. -/
theorem SingularSeriesGaps13501360 :
    (∀ n ∈ Finset.Icc (1350 : ℤ) 1360, (Admissible ({0, n} : Finset ℤ) ↔ Even n)) ∧
      ((Finset.Icc (1350 : ℤ) 1360).filter
        (fun n => Admissible ({0, n} : Finset ℤ))) = {1350, 1352, 1354, 1356, 1358, 1360} := by
  refine ⟨fun n _ => admissible_pair_iff n, ?_⟩
  have h : ((Finset.Icc (1350 : ℤ) 1360).filter
      (fun n => Admissible ({0, n} : Finset ℤ)))
      = (Finset.Icc (1350 : ℤ) 1360).filter (fun n => Even n) := by
    apply Finset.filter_congr
    intro n _
    simpa using admissible_pair_iff n
  rw [h]
  decide

end Brockian

