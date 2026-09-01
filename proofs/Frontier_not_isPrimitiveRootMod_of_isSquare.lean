/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` if every nonzero residue class mod `p`
is a power of `a`, i.e. `a` generates the multiplicative group `(ZMod p)ˣ`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  ∀ x : ZMod p, x ≠ 0 → ∃ n : ℕ, (a : ZMod p) ^ n = x

/-- The set of primes for which `a` is a primitive root. -/
def artinPrimes (a : ℤ) : Set ℕ := {p | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots** (qualitative form): for every integer `a`
which is neither `-1` nor a perfect square, `a` is a primitive root modulo infinitely
many primes. -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬IsSquare a → (artinPrimes a).Infinite

section Results

private lemma natCast_ne_zero_of_lt {p k : ℕ} (hk : 0 < k) (hkp : k < p) :
    ((k : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hk hkp

/-- A perfect square is never a primitive root modulo an odd prime: all its powers are
squares, while an odd prime field always contains a non-square. -/
theorem not_isPrimitiveRootMod_of_isSquare {a : ℤ} (ha : IsSquare a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, rfl⟩ := ha
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rwa [ZMod.ringChar_zmod_n]
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare hchar
  intro h
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (IsSquare.zero)
  obtain ⟨n, hn⟩ := h x hx0
  refine hx ⟨((b : ZMod p)) ^ n, ?_⟩
  rw [← hn]
  push_cast
  rw [mul_pow]

/-- `-1` is a primitive root only modulo `2` and `3`. -/
theorem artinPrimes_neg_one_subset : artinPrimes (-1 : ℤ) ⊆ ({2, 3} : Set ℕ) := by
  intro p hp
  obtain ⟨hp, hprim⟩ := hp
  by_contra hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
  obtain ⟨hne2, hne3⟩ := hmem
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
  have hp5 : 5 ≤ p := by omega
  have hx0 : ((2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) (by omega)
  obtain ⟨n, hn⟩ := hprim ((2 : ℕ) : ZMod p) hx0
  have hcast : (((-1 : ℤ)) : ZMod p) = -1 := by push_cast; ring
  rw [hcast] at hn
  rcases neg_one_pow_eq_or (ZMod p) n with h | h <;> rw [h] at hn
  · have : ((1 : ℕ) : ZMod p) = 0 := by push_cast at hn ⊢; linear_combination -hn
    exact natCast_ne_zero_of_lt (by norm_num) (by omega) this
  · have : ((3 : ℕ) : ZMod p) = 0 := by push_cast at hn ⊢; linear_combination -hn
    exact natCast_ne_zero_of_lt (by norm_num) (by omega) this

/-- A bounded (hence decidable) criterion for being a primitive root. -/
theorem isPrimitiveRootMod_of_bounded {a : ℤ} {p : ℕ}
    (h : ∀ x : ZMod p, x ≠ 0 → ∃ n ∈ Finset.range p, (a : ZMod p) ^ n = x) :
    IsPrimitiveRootMod a p := by
  intro x hx
  obtain ⟨n, -, hn⟩ := h x hx
  exact ⟨n, hn⟩

/-- `2` is a primitive root modulo `5`. -/
theorem two_isPrimitiveRootMod_five : IsPrimitiveRootMod 2 5 :=
  isPrimitiveRootMod_of_bounded (by decide)

/-- `2` is a primitive root modulo `13`. -/
theorem two_isPrimitiveRootMod_thirteen : IsPrimitiveRootMod 2 13 :=
  isPrimitiveRootMod_of_bounded (by decide)

/-- The set of primes witnessing Artin's conjecture for `a = 2` is nonempty. -/
theorem five_mem_artinPrimes_two : 5 ∈ artinPrimes 2 :=
  ⟨by norm_num, two_isPrimitiveRootMod_five⟩

/-- **A Lean-checked reduction for Artin's conjecture**: the two exceptional hypotheses in
Artin's conjecture are exactly the right ones, i.e. they are *necessary*. If `a` is a
primitive root modulo infinitely many primes, then `a ≠ -1` and `a` is not a perfect
square. Consequently `ArtinConjecture` is, for each `a`, a statement about precisely the
integers for which infinitude is not excluded. -/
theorem artin_primitive_root (a : ℤ) (h : (artinPrimes a).Infinite) :
    a ≠ -1 ∧ ¬IsSquare a := by
  constructor
  · rintro rfl
    exact h (Set.Finite.subset (Set.toFinite ({2, 3} : Set ℕ)) artinPrimes_neg_one_subset)
  · intro ha
    obtain ⟨p, hp, hp2⟩ := h.exists_gt 2
    exact not_isPrimitiveRootMod_of_isSquare ha hp.1 (by omega) hp.2

end Results

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

