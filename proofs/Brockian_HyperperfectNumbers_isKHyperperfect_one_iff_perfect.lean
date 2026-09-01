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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect if `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one plus `k` times the
sum of its proper divisors other than `1`.  The definition is stated in the subtraction-free
form `k * σ n + 1 = (k + 1) * n + k`. -/
def IsKHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ 1 < n ∧ k * σ 1 n + 1 = (k + 1) * n + k

/-- `n` is hyperperfect if it is `k`-hyperperfect for some `k ≥ 1`. -/
def IsHyperperfect (n : ℕ) : Prop := ∃ k, IsKHyperperfect k n

/-- `1`-hyperperfect numbers are exactly the perfect numbers (`> 1`). -/
theorem isKHyperperfect_one_iff_perfect {n : ℕ} (hn : 1 < n) :
    IsKHyperperfect 1 n ↔ Nat.Perfect n := by
  have h0 : 0 < n := lt_trans one_pos hn
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul h0, IsKHyperperfect, sigma_one_apply]
  constructor
  · rintro ⟨-, -, h⟩; omega
  · intro h; exact ⟨one_pos, hn, by omega⟩

/-- Geometric sum identity over `ℕ`, in subtraction-free form. -/
private theorem geom_aux (r t : ℕ) :
    r * (∑ k ∈ range t, (r + 1) ^ k) + 1 = (r + 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      calc r * (∑ k ∈ range (t + 1), (r + 1) ^ k) + 1
          = (r * (∑ k ∈ range t, (r + 1) ^ k) + 1) + r * (r + 1) ^ t := by
            rw [Finset.sum_range_succ]; ring
        _ = (r + 1) ^ t + r * (r + 1) ^ t := by rw [ih]
        _ = (r + 1) ^ (t + 1) := by ring

/-- **Minoli's family of hyperperfect numbers.**  If `q` and `p` are primes with
`q ^ t + 1 = p + q` and `t ≥ 2`, then `q ^ (t - 1) * p` is `(q - 1)`-hyperperfect.
For `q = 2` this specializes to the Euclid family of (`1`-hyperperfect) perfect numbers
`2 ^ (t - 1) * (2 ^ t - 1)` associated with Mersenne primes. -/
theorem isKHyperperfect_minoli {q p t : ℕ} (hq : q.Prime) (hp : p.Prime) (ht : 2 ≤ t)
    (hpq : q ^ t + 1 = p + q) :
    IsKHyperperfect (q - 1) (q ^ (t - 1) * p) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  set q := r + 1 with hqdef
  have hr : 1 ≤ r := by have := hq.two_le; omega
  -- `p > q`
  have hq2 : q * q ≤ q ^ t := by
    calc q * q = q ^ 2 := by ring
    _ ≤ q ^ t := Nat.pow_le_pow_right (by omega) ht
  have hpgt : q < p := by nlinarith [hq.two_le]
  have hne : q ≠ p := by omega
  -- factorisation of σ
  have hcop : Nat.Coprime (q ^ (t - 1)) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hp).mpr hne)
  have hsig : σ 1 (q ^ (t - 1) * p) = (∑ k ∈ range t, q ^ k) * (p + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow hq,
      show p = p ^ 1 from (pow_one p).symm, sigma_one_apply_prime_pow hp]
    have h : t - 1 + 1 = t := by omega
    rw [h]
    simp [Finset.sum_range_succ, pow_one, add_comm]
  -- the arithmetic identity
  have hgeom := geom_aux r t
  have hpow : q ^ t = q * q ^ (t - 1) := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega]
    ring
  refine ⟨by omega, ?_, ?_⟩
  · have h1 : 2 ≤ q ^ (t - 1) := by
      calc 2 ≤ q := hq.two_le
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (t - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith [hp.two_le]
  · have hA : (q - 1) * σ 1 (q ^ (t - 1) * p) = (r * ∑ k ∈ range t, q ^ k) * (p + 1) := by
      rw [hsig]; simp [hqdef, mul_assoc]
    rw [hA]
    set A := r * ∑ k ∈ range t, q ^ k with hAdef
    have h1 : A + 1 = q ^ t := hgeom
    have h2 : p + r = A + 1 := by omega
    have h3 : (q - 1 + 1) * (q ^ (t - 1) * p) = (A + 1) * p := by
      rw [show q - 1 + 1 = q by omega, ← mul_assoc, ← hpow, h1]
    rw [h3, show q - 1 = r by omega]
    nlinarith

/-- The Euclid–Mersenne special case: if `2 ^ t - 1` is prime (`t ≥ 2`), then
`2 ^ (t - 1) * (2 ^ t - 1)` is `1`-hyperperfect, i.e. perfect. -/
theorem isKHyperperfect_mersenne {t : ℕ} (ht : 2 ≤ t) (hp : (2 ^ t - 1).Prime) :
    IsKHyperperfect 1 (2 ^ (t - 1) * (2 ^ t - 1)) := by
  have h2 : 2 ≤ 2 ^ t := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) (by omega)
  simpa using isKHyperperfect_minoli Nat.prime_two hp ht (by omega)

/-- **Conditional reduction for the Brockian hyperperfect-infinitude conjecture.**

Fix a prime `q`.  If there are infinitely many exponents `t` for which `q ^ t - q + 1` is
prime, then there are infinitely many hyperperfect numbers.

Taking `q = 2` this says: infinitely many Mersenne primes imply infinitely many
(hyper)perfect numbers.  The unconditional infinitude of hyperperfect numbers is open. -/
theorem HyperperfectInfinitude {q : ℕ} (hq : q.Prime)
    (H : {t : ℕ | 2 ≤ t ∧ (q ^ t - q + 1).Prime}.Infinite) :
    {n : ℕ | IsHyperperfect n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨t, ⟨ht2, htp⟩, htN⟩ := H.exists_gt (N + 1)
  set p := q ^ t - q + 1 with hpdef
  have hqt : q ≤ q ^ t := Nat.le_self_pow (by omega) q
  have hpq : q ^ t + 1 = p + q := by omega
  have hmem : IsHyperperfect (q ^ (t - 1) * p) :=
    ⟨q - 1, isKHyperperfect_minoli hq htp ht2 hpq⟩
  have hbig : N < q ^ (t - 1) * p := by
    have h1 : t - 1 < 2 ^ (t - 1) := Nat.lt_two_pow_self
    have h2 : (2:ℕ) ^ (t - 1) ≤ q ^ (t - 1) := Nat.pow_le_pow_left hq.two_le _
    have h3 : 1 ≤ p := by have := htp.two_le; omega
    calc N < t - 1 := by omega
    _ < 2 ^ (t - 1) := h1
    _ ≤ q ^ (t - 1) := h2
    _ ≤ q ^ (t - 1) * p := Nat.le_mul_of_pos_right _ (by omega)
  exact absurd (hN hmem) (by omega)

/-- Sanity check that the definition is the standard one: `21 = 1 + 2 * (32 - 21 - 1)` is the
smallest `2`-hyperperfect number, obtained from Minoli's family with `q = 3`, `t = 2`, `p = 7`. -/
theorem isKHyperperfect_two_21 : IsKHyperperfect 2 21 :=
  isKHyperperfect_minoli (q := 3) (p := 7) (t := 2) (by norm_num) (by norm_num) le_rfl (by norm_num)

/-- Hyperperfect numbers exist. -/
theorem exists_isHyperperfect : ∃ n, IsHyperperfect n := ⟨21, 2, isKHyperperfect_two_21⟩

end Brockian.HyperperfectNumbers

