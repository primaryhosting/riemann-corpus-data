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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Polignac's conjecture (every even number is the gap of infinitely many pairs of
consecutive primes; in the weak form used here, every even `n` occurs as a
difference of two primes infinitely often) is an open problem.  This file gives a
Lean-checked **conditional reduction**: Polignac's conjecture follows from the
qualitative prime `k`-tuples conjecture of Dickson / Hardy–Littlewood, applied to
the admissible pair `{0, n}`.  Two unconditional complements are also proved: the
degenerate case `n = 0`, and the fact that for odd `n` the corresponding set is
finite (so the evenness hypothesis is exactly right).
-/

namespace Brockian.PolignacPrimes

/-- The Polignac set for a gap `n`: the primes `p` such that `p + n` is also prime.
Polignac's conjecture asserts this set is infinite for every even `n > 0`. -/
def polignacSet (n : ℕ) : Set ℕ := {p | p.Prime ∧ (p + n).Prime}

/-- An integer `m` is a *positive prime* if it is the cast of a prime natural number. -/
def IsPosPrime (m : ℤ) : Prop := ∃ q : ℕ, q.Prime ∧ (q : ℤ) = m

/-- A finite set `H` of integer shifts is *admissible* if for every prime `p` the
reductions of the elements of `H` mod `p` do not cover all residue classes. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The prime `k`-tuples conjecture (Dickson / Hardy–Littlewood, qualitative form):
for every admissible finite set of shifts `H` there are infinitely many integers `m`
such that `m + h` is a (positive) prime for every `h ∈ H`. -/
def PrimeTuplesConjecture : Prop :=
  ∀ H : Finset ℤ, Admissible H → {m : ℤ | ∀ h ∈ H, IsPosPrime (m + h)}.Infinite

/-! ## Admissibility of the pair `{0, n}` for even `n` -/

/-- For even `n`, the pair of shifts `{0, n}` is admissible. -/
theorem admissible_pair_of_even {n : ℕ} (hn : Even n) :
    Admissible ({0, (n : ℤ)} : Finset ℤ) := by
  classical
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases eq_or_lt_of_le hp.two_le with h2 | h2
  · -- `p = 2` : both shifts reduce to `0`, so `1` is a free residue class
    subst_vars
    refine ⟨1, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · rw [Int.cast_zero]; exact zero_ne_one
    · have hz : ((n : ℤ) : ZMod 2) = 0 := by
        push_cast
        exact ZMod.natCast_eq_zero_iff_even.mpr hn
      rw [hz]; exact zero_ne_one
  · -- `p ≥ 3` : two residue classes cannot exhaust `p` of them
    let S : Finset (ZMod p) :=
      ({0, (n : ℤ)} : Finset ℤ).image (fun h : ℤ => ((h : ZMod p)))
    have hcard : S.card < Fintype.card (ZMod p) := by
      have h1 : S.card ≤ (({0, (n : ℤ)} : Finset ℤ)).card := Finset.card_image_le
      have h2' : (({0, (n : ℤ)} : Finset ℤ)).card ≤ 2 := by
        simpa using Finset.card_insert_le (0 : ℤ) {(n : ℤ)}
      have h3 : Fintype.card (ZMod p) = p := ZMod.card p
      omega
    have hex : ∃ r : ZMod p, r ∉ S := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (ZMod p)) ⊆ S := fun r _ => hcon r
      have := Finset.card_le_card hsub
      rw [Finset.card_univ] at this
      omega
    obtain ⟨r, hr⟩ := hex
    refine ⟨r, ?_⟩
    intro h hh hcontra
    exact hr (hcontra ▸ Finset.mem_image_of_mem (fun h : ℤ => ((h : ZMod p))) hh)

/-! ## The conditional reduction -/

/-- **Polignac's conjecture**, conditional on the prime `k`-tuples conjecture:
for every even `n` there are infinitely many primes `p` with `p + n` prime. -/
theorem PolignacConjecture (hHL : PrimeTuplesConjecture) {n : ℕ} (hn : Even n) :
    (polignacSet n).Infinite := by
  have hinf := hHL _ (admissible_pair_of_even hn)
  set T : Set ℤ := {m : ℤ | ∀ h ∈ ({0, (n : ℤ)} : Finset ℤ), IsPosPrime (m + h)} with hT
  have hmem : ∀ m ∈ T, (0 : ℤ) ≤ m ∧ (m.toNat) ∈ polignacSet n := by
    intro m hm
    have h0 : IsPosPrime (m + 0) := hm 0 (by simp)
    have hn' : IsPosPrime (m + (n : ℤ)) := hm (n : ℤ) (by simp)
    obtain ⟨q, hq, hqe⟩ := h0
    obtain ⟨q', hq', hqe'⟩ := hn'
    rw [add_zero] at hqe
    have hm0 : (0 : ℤ) ≤ m := by rw [← hqe]; positivity
    have htn : m.toNat = q := by omega
    refine ⟨hm0, ?_⟩
    simp only [polignacSet, Set.mem_setOf_eq]
    refine ⟨by rw [htn]; exact hq, ?_⟩
    have hq'e : (q' : ℤ) = ((m.toNat + n : ℕ) : ℤ) := by
      push_cast
      rw [hqe', Int.toNat_of_nonneg hm0]
    have : q' = m.toNat + n := by exact_mod_cast hq'e
    rw [← this]; exact hq'
  have hinj : Set.InjOn (fun m : ℤ => m.toNat) T := by
    intro a ha b hb hab
    have h1 := (hmem a ha).1
    have h2 := (hmem b hb).1
    simp only at hab
    omega
  have himg : ((fun m : ℤ => m.toNat) '' T).Infinite := hinf.image hinj
  refine himg.mono ?_
  rintro x ⟨m, hm, rfl⟩
  exact (hmem m hm).2

/-! ## Unconditional complements -/

/-- The case `n = 0` of Polignac's conjecture is Euclid's theorem. -/
theorem polignac_zero : (polignacSet 0).Infinite := by
  have h : polignacSet 0 = {p : ℕ | p.Prime} := by
    ext p; simp [polignacSet]
  rw [h]
  exact Nat.infinite_setOf_prime

/-- Evenness of the gap is necessary: for odd `n`, only `p = 2` can occur, so the
corresponding set of primes is finite. -/
theorem polignacSet_finite_of_odd {n : ℕ} (hn : Odd n) : (polignacSet n).Finite := by
  refine Set.Finite.subset (Set.finite_singleton 2) ?_
  rintro p ⟨hp, hpn⟩
  by_contra hne
  simp only [Set.mem_singleton_iff] at hne
  have hpodd : Odd p := hp.odd_of_ne_two hne
  have heven : Even (p + n) := hpodd.add_odd hn
  have h2 : p + n = 2 := (Nat.Prime.even_iff hpn).mp heven
  have hp2 := hp.two_le
  rcases hn with ⟨k, hk⟩
  omega

end Brockian.PolignacPrimes

