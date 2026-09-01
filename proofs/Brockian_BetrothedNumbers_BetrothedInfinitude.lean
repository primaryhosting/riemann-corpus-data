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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- `IsBetrothed m n` says that `(m, n)` is a *betrothed* (quasi-amicable) pair:
`0 < m < n` and the sum of the divisors of each of `m` and `n`, excluding the number
itself and `1`, equals the other number.  Equivalently `σ m = σ n = m + n + 1`. -/
def IsBetrothed (m n : ℕ) : Prop :=
  0 < m ∧ m < n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

instance decidableIsBetrothed (m n : ℕ) : Decidable (IsBetrothed m n) := by
  unfold IsBetrothed; infer_instance

/-- The set of betrothed pairs. -/
def betrothedPairs : Set (ℕ × ℕ) := {p : ℕ × ℕ | IsBetrothed p.1 p.2}

/-- `(48, 75)` is a betrothed pair: `σ 48 = σ 75 = 124 = 48 + 75 + 1`. -/
theorem isBetrothed_48_75 : IsBetrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> decide

theorem betrothedPairs_nonempty : betrothedPairs.Nonempty :=
  ⟨(48, 75), isBetrothed_48_75⟩

set_option maxRecDepth 40000 in
/-- The seven smallest known betrothed pairs, verified by direct computation. -/
theorem isBetrothed_known_pairs :
    ∀ p ∈ [(48, 75), (140, 195), (1050, 1925), (1575, 1648), (2024, 2295), (5775, 6128),
      (8892, 16587)], IsBetrothed p.1 p.2 := by
  decide

/-- In a betrothed pair the larger member is determined by the smaller one. -/
theorem snd_eq_of_isBetrothed {m n : ℕ} (h : IsBetrothed m n) :
    n = sigma 1 m - m - 1 := by
  have := h.2.2.1
  omega

/-- The first projection is injective on the set of betrothed pairs. -/
theorem injOn_fst_betrothedPairs : Set.InjOn Prod.fst betrothedPairs := by
  rintro ⟨m₁, n₁⟩ h₁ ⟨m₂, n₂⟩ h₂ (hm : m₁ = m₂)
  have e₁ : n₁ = sigma 1 m₁ - m₁ - 1 := snd_eq_of_isBetrothed h₁
  have e₂ : n₂ = sigma 1 m₂ - m₂ - 1 := snd_eq_of_isBetrothed h₂
  simp [hm, e₁, e₂]

/--
**Betrothed Infinitude (reduction).**

There are infinitely many betrothed (quasi-amicable) pairs if and only if the smaller
members of betrothed pairs are unbounded.

Whether either side holds is an open problem; this theorem is the unconditional
equivalence of the two formulations, so producing arbitrarily large betrothed pairs
suffices to establish infinitude.
-/
theorem BetrothedInfinitude :
    (∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsBetrothed m n) ↔ betrothedPairs.Infinite := by
  constructor
  · -- unboundedness of the smaller members forces the set of pairs to be infinite
    intro h hfin
    obtain ⟨N, hN⟩ := (hfin.image Prod.fst).bddAbove
    obtain ⟨m, n, hmN, hmn⟩ := h N
    have hmem : m ∈ Prod.fst '' betrothedPairs := ⟨(m, n), hmn, rfl⟩
    exact absurd (hN hmem) (by omega)
  · -- conversely, a bound on the smaller members forces finiteness
    intro hinf N
    by_contra hcon
    push_neg at hcon
    have hsub : Prod.fst '' betrothedPairs ⊆ Set.Iic N := by
      rintro _ ⟨⟨m, n⟩, hmn, rfl⟩
      by_contra hlt
      exact hcon m n (by simpa using hlt) hmn
    have hfin : (Prod.fst '' betrothedPairs).Finite := (Set.finite_Iic N).subset hsub
    exact hinf (hfin.of_finite_image injOn_fst_betrothedPairs)

end BetrothedNumbers
end Brockian

