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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- `sigmaOne n` is the sum of all positive divisors of `n`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A pair `(m, n)` is *betrothed* (a *quasi-amicable pair*) when `m` and `n` are distinct
positive integers such that the sum of the divisors of each, excluding `1` and the number
itself, equals the other number.  Equivalently `σ m = σ n = m + n + 1`. -/
def IsBetrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- The set of betrothed pairs. -/
def betrothedPairs : Set (ℕ × ℕ) := {p : ℕ × ℕ | IsBetrothed p.1 p.2}

/-- `(48, 75)` is a betrothed pair. -/
theorem isBetrothed_48_75 : IsBetrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- `(140, 195)` is a betrothed pair. -/
theorem isBetrothed_140_195 : IsBetrothed 140 195 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- There is at least one betrothed pair. -/
theorem betrothedPairs_nonempty : betrothedPairs.Nonempty :=
  ⟨(48, 75), isBetrothed_48_75⟩

instance decidableIsBetrothed (m n : ℕ) : Decidable (IsBetrothed m n) := by
  unfold IsBetrothed; infer_instance

/-- The first member of a betrothed pair determines the other one. -/
theorem IsBetrothed.right_unique {m n n' : ℕ} (h : IsBetrothed m n) (h' : IsBetrothed m n') :
    n = n' := by
  obtain ⟨-, -, -, h1, -⟩ := h
  obtain ⟨-, -, -, h2, -⟩ := h'
  omega

/-- The first-coordinate map is injective on the set of betrothed pairs. -/
theorem injOn_fst_betrothedPairs : Set.InjOn Prod.fst betrothedPairs := by
  rintro ⟨m, n⟩ hp ⟨m', n'⟩ hq (h : m = m')
  subst h
  have : n = n' := IsBetrothed.right_unique hp hq
  simp [this]

/-- The candidate partner of `m`: the sum of the divisors of `m` other than `1` and `m`. -/
def betrothedPartner (m : ℕ) : ℕ := sigmaOne m - m - 1

/-- Reformulation of betrothedness in terms of the partner map. -/
theorem isBetrothed_iff {m n : ℕ} :
    IsBetrothed m n ↔
      0 < m ∧ 0 < n ∧ m ≠ n ∧ betrothedPartner m = n ∧ betrothedPartner n = m := by
  unfold IsBetrothed betrothedPartner
  constructor
  · rintro ⟨hm, hn, hmn, h1, h2⟩
    exact ⟨hm, hn, hmn, by omega, by omega⟩
  · rintro ⟨hm, hn, hmn, h1, h2⟩
    exact ⟨hm, hn, hmn, by omega, by omega⟩

/-- The set of numbers that belong to some betrothed pair as the first member. -/
def betrothedFirsts : Set ℕ := {m : ℕ | ∃ n, IsBetrothed m n}

/-- The pair set is infinite exactly when the set of first members is. -/
theorem betrothedPairs_infinite_iff_firsts_infinite :
    betrothedPairs.Infinite ↔ betrothedFirsts.Infinite := by
  constructor
  · intro hinf
    have himg : (Prod.fst '' betrothedPairs).Infinite :=
      hinf.image injOn_fst_betrothedPairs
    refine himg.mono ?_
    rintro x ⟨⟨m, n⟩, hp, rfl⟩
    exact ⟨n, hp⟩
  · intro hinf hfin
    exact hinf (Set.Finite.subset (hfin.image Prod.fst) (by
      rintro m ⟨n, hb⟩
      exact ⟨(m, n), hb, rfl⟩))

/-- No number below `48` is the first member of a betrothed pair: together with
`isBetrothed_48_75`, this shows `(48, 75)` is the smallest betrothed pair. -/
theorem no_betrothed_below_48 : ∀ m n : ℕ, m < 48 → ¬ IsBetrothed m n := by
  intro m n hm hb
  have hn : n = betrothedPartner m := (isBetrothed_iff.mp hb).2.2.2.1.symm
  subst hn
  revert hb
  interval_cases m <;> decide

/-- **Betrothed Infinitude.**  The set of betrothed (quasi-amicable) pairs is infinite if and
only if betrothed pairs occur with arbitrarily large first member.  Whether either side holds
is an open problem; this is the Lean-checked reduction between the two formulations. -/
theorem BetrothedInfinitude :
    betrothedPairs.Infinite ↔ ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothed m n := by
  constructor
  · intro hinf N
    by_contra hcon
    push_neg at hcon
    have hsub : Prod.fst '' betrothedPairs ⊆ Set.Iic N := by
      rintro x ⟨⟨m, n⟩, hp, rfl⟩
      by_contra hx
      exact hcon m n (lt_of_not_ge hx) hp
    exact (hinf.image injOn_fst_betrothedPairs) ((Set.finite_Iic N).subset hsub)
  · intro h hfin
    obtain ⟨N, hN⟩ := (hfin.image (Prod.fst)).bddAbove
    obtain ⟨m, n, hm, hb⟩ := h N
    have : m ≤ N := hN ⟨(m, n), hb, rfl⟩
    omega

end Brockian.BetrothedNumbers

