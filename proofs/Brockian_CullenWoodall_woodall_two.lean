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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is a
-- plain block comment; the identical module docstring is repeated below.)

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

@[simp] lemma woodall_one : woodall 1 = 1 := by norm_num [woodall]

lemma woodall_two : woodall 2 = 7 := by norm_num [woodall]

lemma woodall_three : woodall 3 = 23 := by norm_num [woodall]

lemma woodall_six : woodall 6 = 383 := by norm_num [woodall]

/-- The first few Woodall primes. -/
lemma woodall_prime_two : Nat.Prime (woodall 2) := by rw [woodall_two]; norm_num

lemma woodall_prime_three : Nat.Prime (woodall 3) := by rw [woodall_three]; norm_num

lemma woodall_prime_six : Nat.Prime (woodall 6) := by rw [woodall_six]; norm_num

/-- Woodall numbers grow at least linearly. -/
lemma le_woodall {n : ℕ} (hn : 1 ≤ n) : n ≤ woodall n := by
  have h2 : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : 2 * n ≤ n * 2 ^ n := by
    calc 2 * n = n * 2 := by ring
    _ ≤ n * 2 ^ n := Nat.mul_le_mul_left n h2
  simp only [woodall]
  omega

/-- If `n ≡ 4` or `5 (mod 6)` then `3` divides the Woodall number `W n`. -/
lemma three_dvd_woodall {n : ℕ} (h : n % 6 = 4 ∨ n % 6 = 5) : 3 ∣ woodall n := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, (r = 4 ∨ r = 5) ∧ n = 6 * q + r := by
    exact ⟨n / 6, n % 6, h, by omega⟩
  have hpow : (2 : ℕ) ^ (6 * q + r) = (64 ^ q) * 2 ^ r := by
    rw [pow_add, pow_mul]
    norm_num
  have h64 : 64 ^ q % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hr3 : (6 * q + r) % 3 = r % 3 := by omega
  have key : (6 * q + r) * 2 ^ (6 * q + r) % 3 = 1 := by
    rw [hpow, Nat.mul_mod, Nat.mul_mod (64 ^ q), h64, hr3]
    rcases hr with rfl | rfl <;> norm_num
  have hle : 1 ≤ (6 * q + r) * 2 ^ (6 * q + r) := by
    have h1 : 1 ≤ 6 * q + r := by omega
    have h2 : 1 ≤ 2 ^ (6 * q + r) := Nat.one_le_two_pow
    calc 1 = 1 * 1 := by norm_num
      _ ≤ (6 * q + r) * 2 ^ (6 * q + r) := Nat.mul_le_mul h1 h2
  have hmod : Nat.ModEq 3 1 ((6 * q + r) * 2 ^ (6 * q + r)) := by
    show 1 % 3 = ((6 * q + r) * 2 ^ (6 * q + r)) % 3
    omega
  have := (Nat.modEq_iff_dvd' hle).mp hmod
  simpa [woodall] using this

/-- **Partial (unconditional) result.** No Woodall number with index `n ≡ 4, 5 (mod 6)`
and `n ≥ 4` is prime: it is a proper multiple of `3`. -/
theorem not_prime_woodall_of_mod_six {n : ℕ} (hn : 4 ≤ n) (h : n % 6 = 4 ∨ n % 6 = 5) :
    ¬ Nat.Prime (woodall n) := by
  intro hp
  have hdvd : 3 ∣ woodall n := three_dvd_woodall h
  have h3 : (3 : ℕ) = woodall n := ((Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd).resolve_left
    (by norm_num))
  have hle : n ≤ woodall n := le_woodall (by omega)
  -- but `W n ≥ n * 2 ^ n - 1 > 3` for `n ≥ 4`
  have hbig : 4 * 2 ^ 4 ≤ n * 2 ^ n := by
    have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hn
    exact Nat.mul_le_mul hn this
  have : 3 < woodall n := by
    simp only [woodall]
    omega
  omega

/-- **Conditional reduction (main target).**
If Woodall primes occur with arbitrarily large index — i.e. for every bound `N` there is
some `n ≥ N` with `n * 2 ^ n - 1` prime — then the set of Woodall primes is genuinely
infinite as a set of primes.

The unconditional infinitude of Woodall primes is an open problem, so the hypothesis
cannot presently be discharged; what is proved here is the (nontrivial) step from
unbounded occurrence of prime indices to infinitude of the set of prime *values*,
which uses the growth estimate `n ≤ W n`. -/
theorem WoodallPrimeInfinitude
    (H : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Nat.Prime (woodall n)) :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, woodall n = p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hp⟩ := H (a + 1)
  refine ⟨woodall n, ⟨hp, ⟨n, rfl⟩⟩, ?_⟩
  have := le_woodall (show 1 ≤ n by omega)
  omega

/-- The hypothesis of `WoodallPrimeInfinitude` is in fact *equivalent* to the infinitude of
the set of Woodall primes; so the theorem above is an exact reduction, not a weakening. -/
theorem woodall_prime_indices_unbounded_iff :
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Nat.Prime (woodall n)) ↔
      {p : ℕ | p.Prime ∧ ∃ n : ℕ, woodall n = p}.Infinite := by
  refine ⟨WoodallPrimeInfinitude, fun hS N => ?_⟩
  obtain ⟨p, ⟨hp, n, hn⟩, hnot⟩ := hS.exists_notMem_finset
    ((Finset.range N).image woodall)
  refine ⟨n, ?_, hn ▸ hp⟩
  by_contra hlt
  exact hnot (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), hn⟩)

end Brockian.CullenWoodall

