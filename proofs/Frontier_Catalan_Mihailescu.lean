/-
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The full statement of the Catalan–Mihăilescu theorem: the only pair of consecutive
perfect powers (with bases and exponents at least `2`) is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/
def CatalanMihailescuStatement : Prop :=
  ∀ x y p q : ℕ, 1 < x → 1 < y → 1 < p → 1 < q → x ^ p = y ^ q + 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-- `9 - 8 = 1`: the Catalan pair really is a pair of consecutive perfect powers. -/
theorem catalan_witness : (3 : ℕ) ^ 2 = 2 ^ 3 + 1 := by norm_num

/-- Two squares are never consecutive (for positive bases). -/
theorem sq_ne_sq_add_one (x y : ℕ) (hy : 0 < y) : x ^ 2 ≠ y ^ 2 + 1 := by
  intro h
  have hxy : y < x := by nlinarith
  nlinarith

/-- Easy case of Lebesgue's theorem: `x ^ p = y ^ 2 + 1` is impossible for even `x`. -/
theorem even_pow_ne_sq_add_one {x y p : ℕ} (hx : Even x) (hp : 2 ≤ p) (hy : 0 < y) :
    x ^ p ≠ y ^ 2 + 1 := by
  intro h
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  have h4 : 4 ∣ (m + m) ^ (k + 2) := ⟨(m + m) ^ k * m ^ 2, by ring⟩
  rw [h] at h4
  rcases Nat.even_or_odd y with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · have hn : (n + n) ^ 2 = 4 * n ^ 2 := by ring
    rw [hn] at h4
    omega
  · have hn : (2 * n + 1) ^ 2 = 4 * (n ^ 2 + n) + 1 := by ring
    rw [hn] at h4
    omega

/-- Easy case of Euler's theorem: `x ^ 2 = y ^ q + 1` is impossible for odd `y > 1`. -/
theorem sq_ne_odd_pow_add_one {x y q : ℕ} (hy : Odd y) (hy1 : 1 < y) (hq : 2 ≤ q) :
    x ^ 2 ≠ y ^ q + 1 := by
  intro h
  have hy3 : 3 ≤ y := by
    rcases hy with ⟨t, rfl⟩; omega
  have hyq : Odd (y ^ q) := hy.pow
  have hyq9 : 9 ≤ y ^ q := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ y ^ 2 := Nat.pow_le_pow_left hy3 2
      _ ≤ y ^ q := Nat.pow_le_pow_right (by omega) hq
  have hx2 : 2 ≤ x := by nlinarith
  obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
  have ha1 : 1 ≤ a := by omega
  have hfac : a * (a + 2) = y ^ q := by nlinarith [h]
  have hodd : Odd a := by
    rcases Nat.even_or_odd a with hae | hao
    · exfalso
      have hev : Even (a * (a + 2)) := hae.mul_right _
      rw [hfac] at hev
      rw [Nat.even_iff] at hev
      rw [Nat.odd_iff] at hyq
      omega
    · exact hao
  have hcop : Nat.Coprime a (a + 2) := by
    have hd2 : Nat.gcd a (a + 2) ∣ 2 :=
      (Nat.dvd_add_right (Nat.gcd_dvd_left a (a + 2))).mp (Nat.gcd_dvd_right a (a + 2))
    have hda : Nat.gcd a (a + 2) ∣ a := Nat.gcd_dvd_left _ _
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
    · exact h1
    · exfalso
      rw [h2] at hda
      obtain ⟨t, ht⟩ := hda
      rcases hodd with ⟨u, hu⟩
      omega
  obtain ⟨c, hc⟩ := exists_eq_pow_of_mul_eq_pow (α := ℕ) (Nat.isUnit_iff.mpr hcop) hfac
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (α := ℕ)
    (Nat.isUnit_iff.mpr (Nat.Coprime.symm hcop)) (by rw [mul_comm]; exact hfac)
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | hpos
    · rw [zero_pow (by omega : q ≠ 0)] at hc; omega
    · exact hpos
  have hcd : c < d := by
    by_contra hcon
    push_neg at hcon
    have : d ^ q ≤ c ^ q := Nat.pow_le_pow_left hcon q
    omega
  have key : c ^ q + 3 ≤ (c + 1) ^ q := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
    have h1 : 1 ≤ c ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : c ^ k ≤ (c + 1) ^ k := Nat.pow_le_pow_left (by omega) k
    have e1 : (c + 1) ^ (k + 2) = (c + 1) ^ k * (c ^ 2 + 2 * c + 1) := by ring
    have e2 : c ^ (k + 2) = c ^ k * c ^ 2 := by ring
    have h4 : c ^ k * (c ^ 2 + 2 * c + 1) ≤ (c + 1) ^ k * (c ^ 2 + 2 * c + 1) :=
      Nat.mul_le_mul_right _ h2
    rw [e1, e2]
    nlinarith
  have hle : (c + 1) ^ q ≤ d ^ q := Nat.pow_le_pow_left (by omega) q
  omega

/--
**A Lean-checked reduction of the Catalan–Mihăilescu theorem.**

The full statement follows from the three deep prime-exponent cases:

* `lebesgue` : `x ^ p = y ^ 2 + 1` has no solutions with `x` odd, `p` an odd prime
  (V. A. Lebesgue's theorem);
* `euler` : `x ^ 2 = y ^ q + 1` with `y` even and `q` an odd prime forces `(3, 2, 3)`
  (Euler's case);
* `mihailescu` : `x ^ p = y ^ q + 1` has no solutions with both `p` and `q` odd primes
  (the core of Mihăilescu's theorem).

Everything else — the reduction to prime exponents, the case of two even exponents, the
even-base case of Lebesgue's equation and the odd-`y` case of Euler's equation — is proved here.
-/
theorem Catalan_Mihailescu
    (lebesgue : ∀ x y p : ℕ, Odd x → 1 < x → 1 < y → p.Prime → Odd p → x ^ p ≠ y ^ 2 + 1)
    (euler : ∀ x y q : ℕ, Even y → 1 < x → 1 < y → q.Prime → Odd q → x ^ 2 = y ^ q + 1 →
      x = 3 ∧ y = 2 ∧ q = 3)
    (mihailescu : ∀ x y p q : ℕ, 1 < x → 1 < y → p.Prime → Odd p → q.Prime → Odd q →
      x ^ p ≠ y ^ q + 1) :
    CatalanMihailescuStatement := by
  intro x y p q hx hy hp hq h
  obtain ⟨r, hr, hrp⟩ := Nat.exists_prime_and_dvd (show p ≠ 1 by omega)
  obtain ⟨s, hs, hsq⟩ := Nat.exists_prime_and_dvd (show q ≠ 1 by omega)
  obtain ⟨p', rfl⟩ := hrp
  obtain ⟨q', rfl⟩ := hsq
  have hr2 := hr.two_le
  have hs2 := hs.two_le
  have hp' : 0 < p' := by
    rcases Nat.eq_zero_or_pos p' with rfl | hpos
    · simp at hp
    · exact hpos
  have hq' : 0 < q' := by
    rcases Nat.eq_zero_or_pos q' with rfl | hpos
    · simp at hq
    · exact hpos
  have hX : 1 < x ^ p' := Nat.one_lt_pow (by omega) hx
  have hY : 1 < y ^ q' := Nat.one_lt_pow (by omega) hy
  have hXY : (x ^ p') ^ r = (y ^ q') ^ s + 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm p' r, mul_comm q' s]
    exact h
  rcases hr.eq_two_or_odd' with rfl | hrodd
  · rcases hs.eq_two_or_odd' with rfl | hsodd
    · exact absurd hXY (sq_ne_sq_add_one _ _ (by omega))
    · rcases Nat.even_or_odd (y ^ q') with hYe | hYo
      · obtain ⟨h1, h2, h3⟩ := euler _ _ s hYe hX hY hs hsodd hXY
        obtain ⟨hxa, hxb⟩ : x = 3 ∧ p' = 1 := (Nat.Prime.pow_eq_iff (by norm_num)).mp h1
        obtain ⟨hya, hyb⟩ : y = 2 ∧ q' = 1 := (Nat.Prime.pow_eq_iff (by norm_num)).mp h2
        subst hxb; subst hyb; subst h3
        exact ⟨hxa, by norm_num, hya, by norm_num⟩
      · exact absurd hXY (sq_ne_odd_pow_add_one hYo hY hs2)
  · rcases hs.eq_two_or_odd' with rfl | hsodd
    · rcases Nat.even_or_odd (x ^ p') with hXe | hXo
      · exact absurd hXY (even_pow_ne_sq_add_one (y := y ^ q') hXe hr2 (by omega))
      · exact absurd hXY (lebesgue _ _ r hXo hX hY hr hrodd)
    · exact absurd hXY (mihailescu _ _ r s hX hY hr hrodd hs hsodd)

end Frontier

