import Mathlib
/-!
# Qudit generalized Pauli group (Weyl–Heisenberg) — the "why five" of quantum computing.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. TRUE for every dimension d.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** gate (generalized Pauli X): `X e_j = e_{j+1}` on `ZMod d`. -/
def shift : Matrix (ZMod d) (ZMod d) ℂ := fun i j => if i = j + 1 then 1 else 0

/-- Qudit **clock** gate (generalized Pauli Z): `Z e_j = ω^j e_j`, `ω = exp(2πi/d)`. -/
noncomputable def clock : Matrix (ZMod d) (ZMod d) ℂ :=
  fun i j => if i = j then Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) else 0

/-- Entrywise description of the powers of the shift gate: `X ^ n` sends `e_j` to `e_{j+n}`. -/
private theorem shift_pow_apply (n : ℕ) (i j : ZMod d) :
    ((shift d) ^ n) i j = if i = j + (n : ZMod d) then 1 else 0 := by
  induction n generalizing j with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single (j + 1)]
    · rw [ih]
      simp only [shift]
      push_cast
      ring_nf
    · intro b _ hb
      simp only [shift, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The shift gate has order dividing `d`: `X ^ d = 1`. -/
theorem shift_pow_card : (shift d) ^ d = 1 := by
  ext i j
  rw [shift_pow_apply, Matrix.one_apply]
  simp

/-- `exp (2πi m / d)` only depends on `m` modulo `d`. -/
private theorem exp_mod (m : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m % d : ℕ) : ℂ) / d)
      = Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / d) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  conv_rhs => rw [show m = d * (m / d) + m % d from (Nat.div_add_mod m d).symm]
  push_cast
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((d : ℂ) * ((m / d : ℕ) : ℂ) + ((m % d : ℕ) : ℂ)) / d)
      = 2 * (Real.pi : ℂ) * Complex.I * ((m % d : ℕ) : ℂ) / d
        + ((m / d : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by field_simp; ring]
  rw [Complex.exp_add, Complex.exp_nat_mul]
  simp

/-- Stepping the clock phase: `ω ^ ((j+1).val) = ω * ω ^ (j.val)` with `ω = exp (2πi/d)`. -/
private theorem exp_succ (j : ZMod d) :
    Complex.exp (2 * Real.pi * Complex.I * (((j + 1).val : ℕ) : ℂ) / d)
      = Complex.exp (2 * Real.pi * Complex.I / d)
        * Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℕ) : ℂ) / d) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h1 : (j + 1).val = (j.val + 1) % d := by
    conv_lhs => rw [show j + 1 = ((j.val + 1 : ℕ) : ZMod d) by push_cast [ZMod.natCast_val]; simp]
    rw [ZMod.val_natCast]
  rw [h1, exp_mod, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- The **Weyl–Heisenberg commutation relation**: `Z * X = ω • (X * Z)` with `ω = exp(2πi/d)`.
This is the defining projective-commutation of the qudit generalized Pauli group. -/
theorem clock_shift_weyl :
    clock d * shift d
      = Complex.exp (2 * Real.pi * Complex.I / d) • (shift d * clock d) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, smul_eq_mul,
    Finset.sum_eq_single i, Finset.sum_eq_single j]
  · by_cases h : i = j + 1
    · subst h
      simp only [clock, shift, if_true, mul_one, one_mul]
      exact exp_succ d j
    · simp [clock, shift, h]
  · intro b _ hb
    simp [shift, clock, hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    simp [shift, clock, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ _) h

end BrockianQuantum

