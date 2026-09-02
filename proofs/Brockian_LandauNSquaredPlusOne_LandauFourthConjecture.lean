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

namespace Brockian
namespace LandauNSquaredPlusOne

open Polynomial

/-- **Landau's fourth problem**: there are infinitely many natural numbers `n` such that
`n ^ 2 + 1` is prime. -/
def LandauFourth : Prop := {n : ℕ | Nat.Prime (n ^ 2 + 1)}.Infinite

/-- **Bunyakovsky's conjecture** (in the form used here): if `f : ℤ[X]` is a nonconstant
irreducible integer polynomial with no fixed prime divisor (for each prime `p` there is a
natural number `n` with `p ∤ f n`), then `f` takes prime values at infinitely many natural
numbers. -/
def Bunyakovsky : Prop :=
  ∀ f : ℤ[X], 0 < f.natDegree → Irreducible f →
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ¬ ((p : ℤ) ∣ f.eval (n : ℤ))) →
    {n : ℕ | Prime (f.eval (n : ℤ))}.Infinite

/-! ### The polynomial `X ^ 2 + 1` -/

lemma monic_X_sq_add_one : (X ^ 2 + 1 : ℤ[X]).Monic := by monicity!

lemma natDegree_X_sq_add_one : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by compute_degree!

/-- `X ^ 2 + 1` is irreducible over `ℤ`. -/
lemma irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℤ[X]) := by
  have hm := monic_X_sq_add_one
  have hd := natDegree_X_sq_add_one
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro x hx
  rw [Polynomial.mem_roots hm.ne_zero, IsRoot.def] at hx
  simp only [eval_add, eval_pow, eval_X, eval_one] at hx
  nlinarith [sq_nonneg x]

/-- `X ^ 2 + 1` has no fixed prime divisor: its value at `0` is `1`. -/
lemma no_fixed_prime_divisor_X_sq_add_one (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ¬ ((p : ℤ) ∣ (X ^ 2 + 1 : ℤ[X]).eval (n : ℤ)) := by
  refine ⟨0, ?_⟩
  simp only [Nat.cast_zero, eval_add, eval_pow, eval_X, eval_one]
  intro hdvd
  rw [show ((0 : ℤ) ^ 2 + 1) = 1 by ring] at hdvd
  have := Int.le_of_dvd one_pos hdvd
  have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  omega

/-! ### The conditional theorem -/

/-- **Landau's fourth conjecture**, conditional on Bunyakovsky's conjecture: assuming that
every nonconstant irreducible integer polynomial without a fixed prime divisor takes
infinitely many prime values, there are infinitely many `n : ℕ` with `n ^ 2 + 1` prime.

Landau's fourth problem is open unconditionally; this is a Lean-checked reduction of it to
Bunyakovsky's conjecture. -/
theorem LandauFourthConjecture (hB : Bunyakovsky) : {n : ℕ | Nat.Prime (n ^ 2 + 1)}.Infinite := by
  have h := hB (X ^ 2 + 1) (by rw [natDegree_X_sq_add_one]; norm_num)
    irreducible_X_sq_add_one no_fixed_prime_divisor_X_sq_add_one
  have hset : {n : ℕ | Prime ((X ^ 2 + 1 : ℤ[X]).eval (n : ℤ))}
      = {n : ℕ | Nat.Prime (n ^ 2 + 1)} := by
    ext n
    simp only [Set.mem_setOf_eq, eval_add, eval_pow, eval_X, eval_one]
    rw [show ((n : ℤ) ^ 2 + 1) = ((n ^ 2 + 1 : ℕ) : ℤ) by push_cast; ring,
      ← Nat.prime_iff_prime_int]
  rwa [hset] at h

/-- The same statement in the packaged form `LandauFourth`. -/
theorem landauFourth_of_bunyakovsky (hB : Bunyakovsky) : LandauFourth :=
  LandauFourthConjecture hB

/-! ### Unconditional equivalent reformulations -/

/-- Landau's fourth problem is equivalent to: for every bound `N` there is `n ≥ N` with
`n ^ 2 + 1` prime. -/
theorem landauFourth_iff_forall_exists :
    LandauFourth ↔ ∀ N : ℕ, ∃ n ≥ N, Nat.Prime (n ^ 2 + 1) := by
  constructor
  · intro h N
    obtain ⟨n, hn, hnN⟩ := h.exists_gt N
    exact ⟨n, hnN.le, hn⟩
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨n, hn, hnp⟩ := h (N + 1)
    have := hN hnp
    omega

/-- Landau's fourth problem is equivalent to the infinitude of the set of primes of the
form `n ^ 2 + 1`. -/
theorem landauFourth_iff_primes_infinite :
    LandauFourth ↔ {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 1}.Infinite := by
  have himg : (fun n : ℕ => n ^ 2 + 1) '' {n : ℕ | Nat.Prime (n ^ 2 + 1)}
      = {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 1} := by
    ext p
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨hn, ⟨n, rfl⟩⟩
    · rintro ⟨hp, n, rfl⟩
      exact ⟨n, hp, rfl⟩
  have hinj : Function.Injective (fun n : ℕ => n ^ 2 + 1) := by
    intro a b hab
    simp only [add_left_inj] at hab
    exact Nat.pow_left_injective (by norm_num) hab
  rw [LandauFourth, ← himg, Set.infinite_image_iff hinj.injOn]

end LandauNSquaredPlusOne
end Brockian

