import Mathlib
namespace Brockian.LteTwo

/-- Auxiliary: the integer form of lifting-the-exponent at `p = 2`, phrased with
`emultiplicity`.  This is exactly `Int.two_pow_sub_pow'` from Mathlib. -/
theorem emult_two_pow_sub_pow {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬ (2 : ℤ) ∣ x) :
    emultiplicity 2 (x ^ n - y ^ n) = emultiplicity 2 (x - y) + emultiplicity (2 : ℤ) n :=
  Int.two_pow_sub_pow' n hxy hx

/-- Auxiliary: `Nat.factorization` at a prime equals `padicValNat`. -/
theorem factorization_two (m : ℕ) : m.factorization 2 = padicValNat 2 m := by
  exact Nat.factorization_def m Nat.prime_two

/-- Auxiliary: the natural-number version, phrased with `padicValNat`. -/
theorem padicValNat_two_pow_sub_pow {a b : ℕ} (n : ℕ) (ha : Odd a) (hab : 4 ∣ (a - b))
    (hlt : b < a) (hn : 0 < n) :
    padicValNat 2 (a ^ n - b ^ n) = padicValNat 2 (a - b) + padicValNat 2 n := by
  have hx : ¬ (2 : ℤ) ∣ a := by
    rw [Int.dvd_iff_emod_eq_zero]
    have ha' : a % 2 = 1 := Nat.odd_iff.mp ha
    omega
  have h := emult_two_pow_sub_pow n (by omega : 4 ∣ (a : ℤ) - b) hx
  rw [show (a : ℤ) ^ n - (b : ℤ) ^ n = ((a ^ n - b ^ n : ℕ) : ℤ) from by
        rw [Nat.cast_sub (Nat.pow_le_pow_left hlt.le n)]; rfl,
      show (a : ℤ) - (b : ℤ) = ((a - b : ℕ) : ℤ) from by rw [Nat.cast_sub hlt.le]] at h
  have eq1 : emultiplicity (2 : ℤ) ↑(a ^ n - b ^ n) = ↑(padicValNat 2 (a ^ n - b ^ n)) := by
    rw [padicValNat_eq_emultiplicity (p := 2) (by
      exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hlt hn.ne'))]
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl]
    norm_cast
  have eq2 : emultiplicity (2 : ℤ) ↑(a - b) = ↑(padicValNat 2 (a - b)) := by
    rw [padicValNat_eq_emultiplicity (p := 2) (Nat.sub_ne_zero_of_lt hlt)]
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl]
    norm_cast
  have eq3 : emultiplicity (2 : ℤ) ↑n = ↑(padicValNat 2 n) := by
    rw [padicValNat_eq_emultiplicity (p := 2) hn.ne']
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl]
    norm_cast
  rw [eq1, eq2, eq3] at h
  exact Nat.cast_injective h

/-- Lifting the exponent for p = 2: for odd a,b with 4 ∣ a−b (b < a) and any n > 0,
    v₂(aⁿ − bⁿ) = v₂(a−b) + v₂(n).

    (Adjustment to the original statement: the hypothesis `b ≤ a` is strengthened to
    `b < a`.  With `a = b` the statement is false, since then `aⁿ − bⁿ = 0` and
    `Nat.factorization 0 2 = 0`, while the right-hand side is `v₂(n)`, e.g. `a = b = 1`,
    `n = 2`.  The evenness assumption on `n` mentioned in the informal statement is not
    needed: the conclusion holds for every `n > 0`.  The hypothesis `hb : Odd b` is kept as
    requested, although it is not needed: it follows from `ha` and `hab`.) -/
theorem lte_two {a b n : ℕ} (ha : Odd a) (hb : Odd b) (hab : 4 ∣ (a - b))
    (hlt : b < a) (hn : 0 < n) :
    (a ^ n - b ^ n).factorization 2 = (a - b).factorization 2 + n.factorization 2 := by
  simp only [factorization_two]
  exact padicValNat_two_pow_sub_pow n ha hab hlt hn

end Brockian.LteTwo

