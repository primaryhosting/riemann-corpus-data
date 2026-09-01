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
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is repeated below as a module docstring; Lean 4 does not allow a module
-- docstring to precede the `import` line.)
import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. its multiplicative order is exactly `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop := orderOf ((a : ZMod p)) = p - 1

/-- The set of primes `p` for which `a` is a primitive root modulo `p`. -/
def artinSet (a : ℤ) : Set ℕ := {p | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots.** For every integer `a` which is neither `-1` nor a
perfect square, `a` is a primitive root modulo infinitely many primes. -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (artinSet a).Infinite

/-! ### Elementary facts about the set of primes with `a` as a primitive root -/

/-- A set of naturals is infinite iff it contains arbitrarily large elements. -/
theorem infinite_iff_exists_gt (S : Set ℕ) : S.Infinite ↔ ∀ N : ℕ, ∃ n ∈ S, N < n := by
  constructor
  · intro h N
    obtain ⟨n, hn, hN⟩ := h.exists_gt N
    exact ⟨n, hn, hN⟩
  · intro h hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    obtain ⟨n, hn, hlt⟩ := h N
    exact absurd (hN hn) (by omega)

/-- Reformulation of Artin's conjecture: for each admissible `a` there are arbitrarily large
primes having `a` as a primitive root. -/
theorem artinConjecture_iff :
    ArtinConjecture ↔ ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ,
      ∃ p : ℕ, N < p ∧ p.Prime ∧ IsPrimitiveRootMod a p := by
  unfold ArtinConjecture
  constructor
  · intro h a ha ha' N
    obtain ⟨p, hp, hN⟩ := ((infinite_iff_exists_gt _).1 (h a ha ha')) N
    exact ⟨p, hN, hp.1, hp.2⟩
  · intro h a ha ha'
    refine (infinite_iff_exists_gt _).2 fun N => ?_
    obtain ⟨p, hN, hp, hpr⟩ := h a ha ha' N
    exact ⟨p, ⟨hp, hpr⟩, hN⟩

/-- The order of a nonzero residue divides `p - 1`. -/
theorem orderOf_dvd_sub_one {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    orderOf ((a : ZMod p)) ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha)

/-- **Lucas-type criterion / reduction.** For a prime `p` not dividing `a`, the integer `a` is a
primitive root mod `p` exactly when `a ^ ((p-1)/q) ≢ 1` for every prime `q` dividing `p - 1`.
This reduces membership in `artinSet a` to a finite computation. -/
theorem isPrimitiveRootMod_iff {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    IsPrimitiveRootMod a p ↔
      ∀ q : ℕ, q.Prime → q ∣ (p - 1) → ((a : ZMod p)) ^ ((p - 1) / q) ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  constructor
  · intro h q hq hdvd hpow
    have hdvd' : orderOf ((a : ZMod p)) ∣ (p - 1) / q := orderOf_dvd_of_pow_eq_one hpow
    rw [show orderOf ((a : ZMod p)) = p - 1 from h] at hdvd'
    have hlt : (p - 1) / q < p - 1 := Nat.div_lt_self hp1 hq.one_lt
    have hpos : 0 < (p - 1) / q := Nat.div_pos (Nat.le_of_dvd hp1 hdvd) hq.pos
    exact absurd (Nat.le_of_dvd hpos hdvd') (by omega)
  · intro h
    exact orderOf_eq_of_pow_and_pow_div_prime hp1 (ZMod.pow_card_sub_one_eq_one ha) h

/-! ### The hypotheses of Artin's conjecture are necessary -/

/-- If `a` is a perfect square then it is a primitive root modulo no odd prime; hence the only
possible member of `artinSet a` is `2`. -/
theorem square_not_primitiveRoot {a : ℤ} (hsq : IsSquare a) {p : ℕ} (hp : p ∈ artinSet a) :
    p = 2 := by
  obtain ⟨hpp, hprim⟩ := hp
  haveI : Fact p.Prime := ⟨hpp⟩
  by_contra hne
  have hodd : Odd p := hpp.odd_of_ne_two hne
  obtain ⟨k, hk⟩ := hodd
  have hp2 := hpp.two_le
  obtain ⟨b, hb⟩ := hsq
  have hab : ((a : ZMod p)) = ((b : ZMod p)) ^ 2 := by
    rw [hb]; push_cast; ring
  unfold IsPrimitiveRootMod at hprim
  by_cases hb0 : ((b : ZMod p)) = 0
  · have ha0 : ((a : ZMod p)) = 0 := by rw [hab, hb0]; ring
    rw [ha0] at hprim
    have hz : orderOf (0 : ZMod p) = 0 := by
      apply orderOf_eq_zero
      rw [isOfFinOrder_iff_pow_eq_one]
      rintro ⟨n, hn, hpow⟩
      rw [zero_pow (by omega)] at hpow
      exact zero_ne_one hpow
    rw [hz] at hprim
    omega
  · have key : ((a : ZMod p)) ^ ((p - 1) / 2) = 1 := by
      rw [hab, ← pow_mul]
      have h2 : 2 * ((p - 1) / 2) = p - 1 := by omega
      rw [h2]
      exact ZMod.pow_card_sub_one_eq_one hb0
    have hdvd : orderOf ((a : ZMod p)) ∣ (p - 1) / 2 := orderOf_dvd_of_pow_eq_one key
    rw [hprim] at hdvd
    have hpos : 0 < (p - 1) / 2 := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega

/-- `-1` is a primitive root only modulo primes `p ≤ 3`. -/
theorem neg_one_not_primitiveRoot {p : ℕ} (hp : p ∈ artinSet (-1 : ℤ)) : p ≤ 3 := by
  obtain ⟨hpp, hprim⟩ := hp
  have hsq : (((-1 : ℤ) : ZMod p)) ^ 2 = 1 := by push_cast; ring
  have hdvd : orderOf (((-1 : ℤ) : ZMod p)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  unfold IsPrimitiveRootMod at hprim
  rw [hprim] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-! ### Base cases: `2` is a primitive root modulo `3, 5, 11, 13` -/

theorem two_primitiveRoot_three : IsPrimitiveRootMod 2 3 := by
  unfold IsPrimitiveRootMod
  norm_num
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hd
  have h2 := hq.two_le
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases q
  all_goals (revert hq hd; decide)

theorem two_primitiveRoot_five : IsPrimitiveRootMod 2 5 := by
  unfold IsPrimitiveRootMod
  norm_num
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hd
  have h2 := hq.two_le
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases q
  all_goals (revert hq hd; decide)

theorem two_primitiveRoot_eleven : IsPrimitiveRootMod 2 11 := by
  unfold IsPrimitiveRootMod
  norm_num
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hd
  have h2 := hq.two_le
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases q
  all_goals (revert hq hd; decide)

theorem two_primitiveRoot_thirteen : IsPrimitiveRootMod 2 13 := by
  unfold IsPrimitiveRootMod
  norm_num
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hd
  have h2 := hq.two_le
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases q
  all_goals (revert hq hd; decide)

/-! ### Main statement -/

/-- **Artin's conjecture on primitive roots**, formalized, together with a Lean-checked
reduction and base cases.

1. `ArtinConjecture` is the statement that every integer `a ≠ -1` which is not a perfect square
   is a primitive root modulo infinitely many primes.  It is equivalent to the statement that
   such an `a` is a primitive root modulo arbitrarily large primes.
2. Both exclusions are necessary: a perfect square is a primitive root only modulo `2`, and `-1`
   only modulo primes `p ≤ 3`.
3. Membership of a prime `p` in `artinSet a` reduces to the finite Lucas-type test on the prime
   divisors of `p - 1`.
4. Base cases: `2` is a primitive root modulo `3`, `5`, `11` and `13`. -/
theorem artin_primitive_root :
    (ArtinConjecture ↔ ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ,
        ∃ p : ℕ, N < p ∧ p.Prime ∧ IsPrimitiveRootMod a p) ∧
    (∀ a : ℤ, IsSquare a → ∀ p ∈ artinSet a, p = 2) ∧
    (∀ p ∈ artinSet (-1 : ℤ), p ≤ 3) ∧
    (∀ (a : ℤ) (p : ℕ), p.Prime → (a : ZMod p) ≠ 0 →
        (p ∈ artinSet a ↔ ∀ q : ℕ, q.Prime → q ∣ (p - 1) →
          ((a : ZMod p)) ^ ((p - 1) / q) ≠ 1)) ∧
    ({3, 5, 11, 13} : Set ℕ) ⊆ artinSet 2 := by
  refine ⟨artinConjecture_iff, fun a ha p hp => square_not_primitiveRoot ha hp,
    fun p hp => neg_one_not_primitiveRoot hp, ?_, ?_⟩
  · intro a p hp ha
    have : (p ∈ artinSet a) ↔ (p.Prime ∧ IsPrimitiveRootMod a p) := Iff.rfl
    rw [this, isPrimitiveRootMod_iff hp ha]
    exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
  · intro p hp
    rcases hp with h | h | h | h <;> subst h
    · exact ⟨by norm_num, two_primitiveRoot_three⟩
    · exact ⟨by norm_num, two_primitiveRoot_five⟩
    · exact ⟨by norm_num, two_primitiveRoot_eleven⟩
    · exact ⟨by norm_num, two_primitiveRoot_thirteen⟩

end Frontier

