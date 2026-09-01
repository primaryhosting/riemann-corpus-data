import Mathlib
/-!
# Batch 9 — qudit generalized-Pauli extras (Weyl–Heisenberg, general d). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
variable (d : ℕ) [NeZero d]
def shift : Matrix (ZMod d) (ZMod d) ℂ := fun i j => if i = j + 1 then 1 else 0
noncomputable def clock : Matrix (ZMod d) (ZMod d) ℂ :=
  fun i j => if i = j then Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) else 0

theorem clock_pow_card : (clock d) ^ d = 1 := by
  have hdiag : clock d = Matrix.diagonal
      (fun j : ZMod d => Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [clock, Matrix.diagonal]
    · simp [clock, Matrix.diagonal, h]
  rw [hdiag, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext j
  rw [Pi.pow_apply, ← Complex.exp_nat_mul]
  have h : (d : ℂ) * (2 * Real.pi * Complex.I * (j.val : ℂ) / d)
      = (j.val : ℤ) * (2 * Real.pi * Complex.I) := by
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    field_simp
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

theorem shiftT_shift : (shift d)ᴴ * shift d = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, shift, Matrix.one_apply]
  rw [Finset.sum_eq_single (i + 1)]
  · by_cases h : i = j <;> simp [h]
  · intro b _ hb; simp [hb]
  · intro h; simp at h

theorem clockT_clock : (clock d)ᴴ * clock d = 1 := by
  have key : ∀ x : ZMod d, star (Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / d)) *
      Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / d) = 1 := by
    intro x
    rw [show star (Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / d)) =
        Complex.exp ((starRingEnd ℂ) (2 * Real.pi * Complex.I * (x.val : ℂ) / d)) from
      (Complex.exp_conj _).symm, ← Complex.exp_add]
    have hconj : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (x.val : ℂ) / d)
        = -(2 * Real.pi * Complex.I * (x.val : ℂ) / d) := by
      simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast,
        map_ofNat]
      ring
    rw [hconj, neg_add_cancel, Complex.exp_zero]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, clock, Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simpa using key i
    · simp [h]
  · intro b _ hb; simp [hb]
  · intro h; simp at h

theorem weyl_reverse :
    shift d * clock d = Complex.exp (-(2 * Real.pi * Complex.I / d)) • (clock d * shift d) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  -- the clock phase advances by one step of `exp (2 π i / d)` under `j ↦ j + 1` in `ZMod d`
  have hstep : ∀ j : ZMod d, Complex.exp (2 * Real.pi * Complex.I * ((j + 1).val : ℂ) / d)
      = Complex.exp (2 * Real.pi * Complex.I / d) *
        Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) := by
    intro j
    rw [← Complex.exp_add]
    have hmod : ((j + 1).val : ℕ) ≡ j.val + 1 [MOD d] :=
      (ZMod.natCast_eq_natCast_iff ((j + 1).val) (j.val + 1) d).mp
        (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    obtain ⟨k, hk⟩ : ∃ k : ℤ, ((j.val : ℤ) + 1) - ((j + 1).val : ℤ) = d * k := by
      obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd (n := d) (a := (j + 1).val) (b := j.val + 1)).mp hmod
      exact ⟨k, by push_cast at hk ⊢; linarith⟩
    have hc : ((j.val : ℂ) + 1) / (d : ℂ) - (((j + 1).val : ℕ) : ℂ) / (d : ℂ) = (k : ℂ) := by
      have h2 : ((j.val : ℂ) + 1) - (((j + 1).val : ℕ) : ℂ) = (d : ℂ) * (k : ℂ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hk
      field_simp
      linear_combination h2
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-k, by push_cast; linear_combination (-(2 * (Real.pi : ℂ) * Complex.I)) * hc⟩
  ext i j
  rw [Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · simp only [shift, clock]
    by_cases h : i = j + 1
    · subst h
      rw [if_pos rfl, hstep j, Complex.exp_neg]
      field_simp
      simp [mul_comm]
    · rw [if_neg h]; ring
  · intro b _ hb; simp [clock, Ne.symm hb]
  · intro h; simp at h
  · intro b _ hb; simp [clock, hb]
  · intro h; simp at h

theorem clock_off_diag : ∀ i j, i ≠ j → clock d i j = 0 := by
  intro i j h; simp [clock, h]

theorem shift_off_diag : ∀ i j, ¬ (i = j + 1) → shift d i j = 0 := by
  intro i j h; simp [shift, h]

theorem clock_diag_apply : ∀ i, clock d i i = Complex.exp (2 * Real.pi * Complex.I * (i.val : ℂ) / d) := by
  intro i; simp [clock]
end BrockianQuantum

