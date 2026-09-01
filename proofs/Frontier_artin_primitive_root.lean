/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Frontier

/-- `IsPrimitiveRootMod a p` says that the integer `a` is a primitive root modulo `p`,
i.e. the residue class of `a` generates the multiplicative group `(ZMod p)ˣ`, which for
a prime `p` amounts to saying that `a` has multiplicative order `p - 1` in `ZMod p`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop := orderOf ((a : ZMod p)) = p - 1

/-- **Artin's conjecture on primitive roots**: every integer `a` which is neither `-1` nor a
perfect square is a primitive root modulo infinitely many primes. -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Infinite

/-- **Key intermediate lemma (primitive-root criterion).** For a prime `p`, an integer `a` is a
primitive root modulo `p` exactly when `a` is invertible mod `p` and `a ^ ((p-1)/q) ≢ 1` for every
prime `q` dividing `p - 1`. This turns the (a priori non-computable) condition
`orderOf (a : ZMod p) = p - 1` into a finite, decidable check. -/
theorem isPrimitiveRootMod_iff {a : ℤ} {p : ℕ} (hp : p.Prime) :
    IsPrimitiveRootMod a p ↔
      (a : ZMod p) ≠ 0 ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 → ((a : ZMod p)) ^ ((p - 1) / q) ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  constructor
  · intro h
    have hpow : ((a : ZMod p)) ^ (p - 1) = 1 := by
      rw [← h]; exact pow_orderOf_eq_one _
    refine ⟨?_, ?_⟩
    · intro h0
      rw [h0, zero_pow (by omega)] at hpow
      exact zero_ne_one hpow
    · intro q hq hqd hcon
      have hdvd : (p - 1) ∣ (p - 1) / q := by
        rw [← h]; exact orderOf_dvd_of_pow_eq_one hcon
      have hq2 := hq.two_le
      have hlt : (p - 1) / q < p - 1 := Nat.div_lt_self hp1 (by omega)
      have hpos : 0 < (p - 1) / q := Nat.div_pos (Nat.le_of_dvd hp1 hqd) (by omega)
      exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  · rintro ⟨h0, hq⟩
    exact orderOf_eq_of_pow_and_pow_div_prime hp1 (ZMod.pow_card_sub_one_eq_one h0) hq

/-- **A Lean-checked reduction of Artin's conjecture.** The conjecture is equivalent to the
statement that for every admissible `a` and every bound `N` one can find a prime `p > N` passing
the elementary primitive-root test of `isPrimitiveRootMod_iff`. -/
theorem artin_conjecture_iff_unbounded :
    ArtinConjecture ↔
      ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
        (a : ZMod p) ≠ 0 ∧
          ∀ q : ℕ, q.Prime → q ∣ p - 1 → ((a : ZMod p)) ^ ((p - 1) / q) ≠ 1 := by
  constructor
  · intro h a ha hsq N
    obtain ⟨p, hp, hNp⟩ := (h a ha hsq).exists_gt N
    obtain ⟨hp1, hp2⟩ := hp
    exact ⟨p, hNp, hp1, ((isPrimitiveRootMod_iff hp1).1 hp2).1,
      ((isPrimitiveRootMod_iff hp1).1 hp2).2⟩
  · intro h a ha hsq
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨p, hNp, hp, h0, hq⟩ := h a ha hsq N
    exact ⟨p, ⟨hp, (isPrimitiveRootMod_iff hp).2 ⟨h0, hq⟩⟩, hNp⟩

/-- Base cases: `2` is a primitive root modulo each of the primes `3, 5, 11, 13, 19, 29`. -/
theorem two_isPrimitiveRootMod_base :
    ∀ p ∈ ({3, 5, 11, 13, 19, 29} : Finset ℕ), p.Prime ∧ IsPrimitiveRootMod 2 p := by
  intro p hp
  fin_cases hp <;>
    refine ⟨by norm_num, (isPrimitiveRootMod_iff (by norm_num)).2 ⟨by decide, ?_⟩⟩ <;>
    · intro q hq hqd
      have h1 : q ≤ _ := Nat.le_of_dvd (by norm_num) hqd
      have h2 : 2 ≤ q := hq.two_le
      interval_cases q <;> revert hqd <;> decide

/-- **Artin's primitive root theorem package.**

* the first component states Artin's conjecture and reduces it, unconditionally, to an
  elementary unbounded search using the primitive-root criterion;
* the second component verifies the base cases: `2` is a primitive root modulo
  `3, 5, 11, 13, 19, 29`.
-/
theorem artin_primitive_root :
    (ArtinConjecture ↔
      ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
        (a : ZMod p) ≠ 0 ∧
          ∀ q : ℕ, q.Prime → q ∣ p - 1 → ((a : ZMod p)) ^ ((p - 1) / q) ≠ 1) ∧
    (∀ p ∈ ({3, 5, 11, 13, 19, 29} : Finset ℕ), p.Prime ∧ IsPrimitiveRootMod 2 p) :=
  ⟨artin_conjecture_iff_unbounded, two_isPrimitiveRootMod_base⟩

end Frontier

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

