/-
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-! ## Auxiliary: periodicity of powers in `ZMod N` -/

/-- If `a ^ d = 1` then `a ^ n` only depends on `n % d`. -/
private lemma pow_eq_pow_mod {M : Type*} [Monoid M] (a : M) {d : ℕ} (hd : a ^ d = 1) (n : ℕ) :
    a ^ n = a ^ (n % d) := by
  conv_lhs => rw [← Nat.div_add_mod n d, pow_add, pow_mul, hd, one_pow, one_mul]

/-! ## The base case: consecutive powers of `2` and `3` (Levi ben Gerson) -/

/-- **Base case, first direction.** The only solution of `3 ^ m = 2 ^ n + 1` with `m, n > 1`
is `9 = 8 + 1`. -/
theorem three_pow_eq_two_pow_succ_iff {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    3 ^ m = 2 ^ n + 1 ↔ (m = 2 ∧ n = 3) := by
  constructor
  · intro h
    -- First, `n ≥ 3`.
    have hn3 : 3 ≤ n := by
      rcases Nat.lt_or_ge n 3 with h3 | h3
      · interval_cases n
        · -- n = 2 : 3 ^ m = 5, impossible since 3 ^ m ≥ 9
          exfalso
          have : (3:ℕ) ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
          omega
      · exact h3
    -- Work modulo 8 : `3 ^ m ≡ 1`, hence `m` is even.
    have h8 : ((3:ZMod 8)) ^ m = 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = 3 + k := ⟨n - 3, by omega⟩
      have hc := congrArg (Nat.cast : ℕ → ZMod 8) h
      push_cast at hc
      have hz : ((2:ZMod 8)) ^ (3 + k) = 0 := by
        rw [pow_add, show ((2:ZMod 8)) ^ 3 = 0 from by decide, zero_mul]
      rw [hz, zero_add] at hc
      exact hc
    have hmeven : m % 2 = 0 := by
      rw [pow_eq_pow_mod (d := 2) (3 : ZMod 8) (by decide) m] at h8
      have hcase : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases hcase with h' | h'
      · exact h'
      · rw [h'] at h8; exact absurd h8 (by decide)
    -- If `n = 3` we are done; otherwise `n ≥ 4`.
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · have hn' : n = 3 := by omega
      subst hn'
      refine ⟨?_, rfl⟩
      have h9 : (3:ℕ) ^ m = 3 ^ 2 := by norm_num at h ⊢; omega
      exact Nat.pow_right_injective (by norm_num) h9
    · exfalso
      -- Modulo 16 : `3 ^ m ≡ 1`, hence `4 ∣ m`.
      have h16 : ((3:ZMod 16)) ^ m = 1 := by
        obtain ⟨k, rfl⟩ : ∃ k, n = 4 + k := ⟨n - 4, by omega⟩
        have hc := congrArg (Nat.cast : ℕ → ZMod 16) h
        push_cast at hc
        have hz : ((2:ZMod 16)) ^ (4 + k) = 0 := by
          rw [pow_add, show ((2:ZMod 16)) ^ 4 = 0 from by decide, zero_mul]
        rw [hz, zero_add] at hc
        exact hc
      have hm4 : m % 4 = 0 := by
        rw [pow_eq_pow_mod (d := 4) (3 : ZMod 16) (by decide) m] at h16
        have hcase : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
        rcases hcase with h' | h' | h' | h' <;> rw [h'] at h16
        · exact h'
        all_goals exact absurd h16 (by decide)
      -- Modulo 5 : `3 ^ m = 1`, so `2 ^ n = 0`, impossible.
      have h5 : ((2:ZMod 5)) ^ n = 0 := by
        have hc := congrArg (Nat.cast : ℕ → ZMod 5) h
        push_cast at hc
        have h3 : ((3:ZMod 5)) ^ m = 1 := by
          rw [pow_eq_pow_mod (d := 4) (3 : ZMod 5) (by decide) m, hm4, pow_zero]
        rw [h3] at hc
        linear_combination -hc
      rw [pow_eq_pow_mod (d := 4) (2 : ZMod 5) (by decide) n] at h5
      have hcase : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases hcase with h' | h' | h' | h' <;> rw [h'] at h5 <;> exact absurd h5 (by decide)
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- **Base case, second direction.** There is no solution of `2 ^ n = 3 ^ m + 1`
with `m > 1` (no hypothesis on `n` is needed). -/
theorem two_pow_ne_three_pow_succ {m n : ℕ} (hm : 1 < m) :
    2 ^ n ≠ 3 ^ m + 1 := by
  intro h
  -- Modulo 9 : `2 ^ n ≡ 1`, hence `6 ∣ n`.
  have h9 : ((2:ZMod 9)) ^ n = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, m = 2 + k := ⟨m - 2, by omega⟩
    subst hk
    have hc := congrArg (Nat.cast : ℕ → ZMod 9) h
    push_cast at hc
    have hz : ((3:ZMod 9)) ^ (2 + k) = 0 := by
      rw [pow_add, show ((3:ZMod 9)) ^ 2 = 0 from by decide, zero_mul]
    rw [hz, zero_add] at hc
    exact hc
  have hn6 : n % 6 = 0 := by
    rw [pow_eq_pow_mod (d := 6) (2 : ZMod 9) (by decide) n] at h9
    have hcase : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
      omega
    rcases hcase with h' | h' | h' | h' | h' | h' <;> rw [h'] at h9
    · exact h'
    all_goals exact absurd h9 (by decide)
  -- Modulo 7 : `2 ^ n = 1` since `3 ∣ n`, hence `3 ^ m = 0`, impossible.
  have hn3 : n % 3 = 0 := by omega
  have h7 : ((3:ZMod 7)) ^ m = 0 := by
    have hc := congrArg (Nat.cast : ℕ → ZMod 7) h
    push_cast at hc
    have h2 : ((2:ZMod 7)) ^ n = 1 := by
      rw [pow_eq_pow_mod (d := 3) (2 : ZMod 7) (by decide) n, hn3, pow_zero]
    rw [h2] at hc
    linear_combination -hc
  rw [pow_eq_pow_mod (d := 6) (3 : ZMod 7) (by decide) m] at h7
  have hcase : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by omega
  rcases hcase with h' | h' | h' | h' | h' | h' <;> rw [h'] at h7 <;> exact absurd h7 (by decide)

/-! ## An unconditional special case: no two consecutive perfect squares -/

/-- Two positive perfect squares are never consecutive. -/
theorem sq_ne_sq_succ {A B : ℕ} (hB : 0 < B) : A ^ 2 ≠ B ^ 2 + 1 := by
  intro h
  have hAB : B < A := by nlinarith
  nlinarith

/-- **Unconditional special case of Catalan.** If both exponents are even there is no solution
of `x ^ m = y ^ n + 1` (with `y > 0`), since two positive squares are never consecutive. -/
theorem catalan_even_exponents {x y a b : ℕ} (hy : 0 < y) :
    x ^ (2 * a) ≠ y ^ (2 * b) + 1 := by
  rw [Nat.mul_comm 2 a, Nat.mul_comm 2 b, pow_mul, pow_mul]
  exact sq_ne_sq_succ (pow_pos hy b)

/-! ## Statement of Catalan's conjecture and the reduction to prime exponents -/

/-- Catalan's conjecture (Mihailescu's theorem): the only pair of consecutive perfect powers
(with exponents `> 1` and bases `> 1`) is `9 = 3 ^ 2` and `8 = 2 ^ 3`. -/
def CatalanConjecture : Prop :=
  ∀ x y m n : ℕ, 1 < x → 1 < y → 1 < m → 1 < n → x ^ m = y ^ n + 1 →
    x = 3 ∧ m = 2 ∧ y = 2 ∧ n = 3

/-- Catalan's conjecture restricted to *prime* exponents. -/
def CatalanConjecturePrimeExponents : Prop :=
  ∀ x y p q : ℕ, 1 < x → 1 < y → p.Prime → q.Prime → x ^ p = y ^ q + 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-- **Reduction to prime exponents.** The general form of Catalan's conjecture follows from the
prime-exponent form. -/
theorem catalan_of_catalan_prime_exponents :
    CatalanConjecturePrimeExponents → CatalanConjecture := by
  intro H x y m n hx hy hm hn h
  obtain ⟨p, hp, k, rfl⟩ : ∃ p, p.Prime ∧ ∃ k, m = p * k := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := m) (by omega)
    obtain ⟨k, hk⟩ := hpd
    exact ⟨p, hp, k, hk⟩
  obtain ⟨q, hq, j, rfl⟩ : ∃ q, q.Prime ∧ ∃ j, n = q * j := by
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
    obtain ⟨j, hj⟩ := hqd
    exact ⟨q, hq, j, hj⟩
  have hk0 : k ≠ 0 := by rintro rfl; simp at hm
  have hj0 : j ≠ 0 := by rintro rfl; simp at hn
  have hX : 1 < x ^ k := Nat.one_lt_pow hk0 hx
  have hY : 1 < y ^ j := Nat.one_lt_pow hj0 hy
  have key : (x ^ k) ^ p = (y ^ j) ^ q + 1 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm k p, Nat.mul_comm j q]
    exact h
  obtain ⟨hx3, hp2, hy2, hq3⟩ := H _ _ _ _ hX hY hp hq key
  have hk1 : x = 3 ∧ k = 1 := (Nat.Prime.pow_eq_iff (by norm_num)).1 hx3
  have hj1 : y = 2 ∧ j = 1 := (Nat.Prime.pow_eq_iff (by norm_num)).1 hy2
  refine ⟨hk1.1, ?_, hj1.1, ?_⟩
  · rw [hp2, hk1.2]
  · rw [hq3, hj1.2]

/-! ## Main target -/

/--
**Catalan / Mihailescu.**

Mihailescu's theorem states that `8` and `9` are the only consecutive perfect powers, i.e. the
only solution of `x ^ m - y ^ n = 1` in integers `x, y, m, n > 1` is `3 ^ 2 - 2 ^ 3 = 1`.

A full formal proof is out of reach here (it requires cyclotomic fields and Mihailescu's
ideal-theoretic arguments; the statement is not available in Mathlib). This target therefore
records:

* the **base case** (Levi ben Gerson, 1343): among powers of `2` and `3` with exponents `> 1`, the
  only consecutive pair is `8, 9` — proved unconditionally, in both directions;
* the unconditional special case of **even exponents** (no two positive squares are consecutive);
* a **Lean-checked reduction**: the general statement follows from the prime-exponent statement.
-/
theorem Catalan_Mihailescu :
    (∀ m n : ℕ, 1 < m → 1 < n → (3 ^ m = 2 ^ n + 1 ↔ (m = 2 ∧ n = 3))) ∧
    (∀ m n : ℕ, 1 < m → 2 ^ n ≠ 3 ^ m + 1) ∧
    (∀ x y a b : ℕ, 0 < y → x ^ (2 * a) ≠ y ^ (2 * b) + 1) ∧
    (CatalanConjecturePrimeExponents → CatalanConjecture) :=
  ⟨fun _ _ hm hn => three_pow_eq_two_pow_succ_iff hm hn,
   fun _ _ hm => two_pow_ne_three_pow_succ hm,
   fun _ _ _ _ hy => catalan_even_exponents hy,
   catalan_of_catalan_prime_exponents⟩

#print axioms Catalan_Mihailescu

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

