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

set_option grind.warning false

/-!
# Landau's Fourth Problem — Conditional Reduction

CONDITIONAL: infinitude of primes of the form `n ^ 2 + 1` assuming Bunyakovsky's conjecture.

This module packages the AXLE-verified reduction theorem
`Brockian.LandauNSquaredPlusOneReduction.LandauFourthConjecture`, a genuine proven implication
`BunyakovskyConjecture → LandauFourthStatement`. `BunyakovskyConjecture` is a separate, open
hypothesis; the conclusion is not proved unconditionally.
-/

namespace Brockian.LandauNSquaredPlusOneReduction

open Polynomial

/-- Landau's fourth problem: there are infinitely many primes of the form `n ^ 2 + 1`,
phrased as "for every bound `N` there is some `n > N` with `n ^ 2 + 1` prime". -/
def LandauFourthStatement : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (n ^ 2 + 1)

/-- Bunyakovsky's conjecture: an integer polynomial `f` of positive degree with positive
leading coefficient, which is irreducible and has no fixed prime divisor (i.e. for every
prime `p` some value `f(m)`, `m : ℕ`, is not divisible by `p`), takes prime values
infinitely often on the natural numbers. -/
def BunyakovskyConjecture : Prop :=
  ∀ f : Polynomial ℤ, 0 < f.natDegree → 0 < f.leadingCoeff → Irreducible f →
    (∀ p : ℕ, p.Prime → ∃ m : ℕ, ¬ ((p : ℤ) ∣ f.eval (m : ℤ))) →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Prime (f.eval (n : ℤ))

/-- `X ^ 2 + 1` is irreducible in `ℤ[X]`. -/
theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : Polynomial ℤ) := by
  have hmZ : (X ^ 2 + 1 : Polynomial ℤ).Monic := by monicity!
  refine hmZ.irreducible_of_irreducible_map (Int.castRingHom ℚ) _ ?_
  have hmap : ((X ^ 2 + 1 : Polynomial ℤ).map (Int.castRingHom ℚ)) = (X ^ 2 + 1 : Polynomial ℚ) := by
    simp [Polynomial.map_add, Polynomial.map_pow]
  rw [hmap]
  have hm : (X ^ 2 + 1 : Polynomial ℚ).Monic := by monicity!
  have hd : (X ^ 2 + 1 : Polynomial ℚ).natDegree = 2 := by compute_degree!
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro x hx
  rw [Polynomial.mem_roots hm.ne_zero] at hx
  have h : x ^ 2 + 1 = 0 := by simpa [IsRoot.def] using hx
  nlinarith [sq_nonneg x]

/-- The polynomial `X ^ 2 + 1` has natural degree `2`. -/
theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : Polynomial ℤ).natDegree = 2 := by
  compute_degree!

/-- The polynomial `X ^ 2 + 1` has leading coefficient `1`. -/
theorem leadingCoeff_X_sq_add_one : (X ^ 2 + 1 : Polynomial ℤ).leadingCoeff = 1 := by
  have hmZ : (X ^ 2 + 1 : Polynomial ℤ).Monic := by monicity!
  exact hmZ

/-- Evaluating `X ^ 2 + 1` at a natural number. -/
theorem eval_X_sq_add_one (n : ℕ) :
    (X ^ 2 + 1 : Polynomial ℤ).eval (n : ℤ) = ((n ^ 2 + 1 : ℕ) : ℤ) := by
  push_cast
  simp

/-- `X ^ 2 + 1` has no fixed prime divisor: no prime divides all of its values,
since its value at `0` is `1`. -/
theorem no_fixed_prime_divisor (p : ℕ) (hp : p.Prime) :
    ∃ m : ℕ, ¬ ((p : ℤ) ∣ (X ^ 2 + 1 : Polynomial ℤ).eval (m : ℤ)) := by
  refine ⟨0, ?_⟩
  simp only [eval_X_sq_add_one]
  norm_num
  intro hdvd
  have : p ∣ 1 := by exact_mod_cast hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- **Conditional reduction of Landau's fourth problem.**
Bunyakovsky's conjecture implies that there are infinitely many primes of the form
`n ^ 2 + 1`. -/
theorem LandauFourthConjecture (hB : BunyakovskyConjecture) : LandauFourthStatement := by
  intro N
  obtain ⟨n, hn, hprime⟩ :=
    hB (X ^ 2 + 1) (by rw [natDegree_X_sq_add_one]; norm_num)
      (by rw [leadingCoeff_X_sq_add_one]; norm_num) irreducible_X_sq_add_one
      no_fixed_prime_divisor N
  refine ⟨n, hn, ?_⟩
  rw [eval_X_sq_add_one] at hprime
  exact Nat.prime_iff_prime_int.2 hprime

end Brockian.LandauNSquaredPlusOneReduction
