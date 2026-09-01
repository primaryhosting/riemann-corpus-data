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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Landau's fourth problem asks whether there are infinitely many primes of the form
`n ^ 2 + 1`.  This is an open problem, so what is formalized here is

* a **conditional reduction**: Landau's fourth conjecture follows from the
  Bunyakovsky conjecture (`LandauFourthConjecture`), together with the
  verification that `X ^ 2 + 1` satisfies all hypotheses of that conjecture; and
* two **unconditional partial results**: every prime of the form `n ^ 2 + 1` is
  either `2` or congruent to `1` mod `4`, and infinitely many primes divide some
  value `n ^ 2 + 1`.
-/

namespace Brockian.LandauNSquaredPlusOne

open Polynomial

/-- The set of natural numbers `n` for which `n ^ 2 + 1` is prime. -/
def LandauSet : Set ℕ := {n : ℕ | Nat.Prime (n ^ 2 + 1)}

/-- **Bunyakovsky's conjecture** (also known as Bouniakowsky's conjecture): if
`f ∈ ℤ[X]` is irreducible, of positive degree, with positive leading coefficient,
and the values `f(0), f(1), f(2), …` have no common divisor `> 1`, then `f(n)` is
prime for infinitely many natural numbers `n`. -/
def BunyakovskyConjecture : Prop :=
  ∀ f : ℤ[X], 0 < f.natDegree → Irreducible f → 0 < f.leadingCoeff →
    (∀ d : ℕ, 1 < d → ∃ n : ℕ, ¬ ((d : ℤ) ∣ f.eval (n : ℤ))) →
    {n : ℕ | Prime (f.eval (n : ℤ))}.Infinite

section Polynomial

/-- The polynomial `X ^ 2 + 1` over `ℤ` is monic. -/
theorem monic_X_sq_add_one : (X ^ 2 + 1 : ℤ[X]).Monic := by
  monicity!

/-- The polynomial `X ^ 2 + 1` over `ℤ` has degree `2`. -/
theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by
  compute_degree!

/-- The polynomial `X ^ 2 + 1` is irreducible over `ℤ`. -/
theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℤ[X]) := by
  have hd := natDegree_X_sq_add_one
  rw [monic_X_sq_add_one.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by omega) (by omega)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro a ha
  rw [mem_roots (by intro h; simpa using congrArg (Polynomial.eval 0) h)] at ha
  have h : a ^ 2 + 1 = 0 := by simpa [IsRoot] using ha
  nlinarith [sq_nonneg a]

/-- Evaluating `X ^ 2 + 1` at a natural number `n`. -/
theorem eval_X_sq_add_one (n : ℕ) :
    (X ^ 2 + 1 : ℤ[X]).eval (n : ℤ) = ((n ^ 2 + 1 : ℕ) : ℤ) := by
  push_cast
  simp

end Polynomial

/-- `X ^ 2 + 1` has no fixed prime divisor: for every `d > 1` some value
`n ^ 2 + 1` is not divisible by `d` (take `n = 0`). -/
theorem no_fixed_divisor (d : ℕ) (hd : 1 < d) :
    ∃ n : ℕ, ¬ ((d : ℤ) ∣ (X ^ 2 + 1 : ℤ[X]).eval (n : ℤ)) := by
  refine ⟨0, ?_⟩
  rw [eval_X_sq_add_one]
  intro h
  have : (d : ℤ) ∣ 1 := by simpa using h
  have := Int.le_of_dvd one_pos this
  omega

/-- **Landau's fourth conjecture, conditionally on Bunyakovsky's conjecture.**
If Bunyakovsky's conjecture holds, then there are infinitely many natural numbers
`n` such that `n ^ 2 + 1` is prime. -/
theorem LandauFourthConjecture (H : BunyakovskyConjecture) : LandauSet.Infinite := by
  have hinf := H (X ^ 2 + 1) (by rw [natDegree_X_sq_add_one]; omega)
    irreducible_X_sq_add_one (by rw [monic_X_sq_add_one.leadingCoeff]; norm_num)
    no_fixed_divisor
  have hset : {n : ℕ | Prime ((X ^ 2 + 1 : ℤ[X]).eval (n : ℤ))} = LandauSet := by
    ext n
    simp only [Set.mem_setOf_eq, LandauSet, eval_X_sq_add_one]
    rw [Int.prime_iff_natAbs_prime, Int.natAbs_natCast]
  rwa [hset] at hinf

/-! ### Unconditional partial results -/

/-- Every prime of the form `n ^ 2 + 1` is either `2` or congruent to `1` mod `4`. -/
theorem prime_sq_add_one_eq_two_or_one_mod_four (n : ℕ) (hp : Nat.Prime (n ^ 2 + 1)) :
    n ^ 2 + 1 = 2 ∨ (n ^ 2 + 1) % 4 = 1 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · right
    have : n ^ 2 + 1 = 4 * k ^ 2 + 1 := by subst hk; ring
    omega
  · left
    have hdvd : 2 ∣ n ^ 2 + 1 := ⟨2 * k ^ 2 + 2 * k + 1, by subst hk; ring⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdvd) with h | h
    · omega
    · omega

/-- Unconditionally, infinitely many primes divide some value of `n ^ 2 + 1`. -/
theorem infinite_primes_dividing_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  refine Set.Infinite.mono ?_ (Nat.infinite_setOf_prime_modEq_one (k := 4) (by norm_num))
  rintro p ⟨hp, hmod⟩
  refine ⟨hp, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp4 : p % 4 ≠ 3 := by
    have : p % 4 = 1 % 4 := hmod
    omega
  obtain ⟨x, hx⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 hp4
  refine ⟨x.val, ?_⟩
  have : ((x.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    rw [pow_two, ← hx]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 this

end Brockian.LandauNSquaredPlusOne

