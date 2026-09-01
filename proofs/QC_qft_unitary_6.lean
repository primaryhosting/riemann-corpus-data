import Mathlib

/-!
# Unitarity of the 6-qubit Quantum Fourier Transform

The quantum Fourier transform on `n = 6` qubits acts on the `2^6 = 64` dimensional
state space.  Its matrix has entries

`F j k = (1 / √64) * exp (2πi * j * k / 64) = (1/8) * exp (2πi * j * k / 64)`.

We prove that this matrix is unitary, i.e. it belongs to `Matrix.unitaryGroup (Fin 64) ℂ`.
-/

namespace QC

open Complex Finset

/-- The `6`-qubit quantum Fourier transform matrix, acting on the `2 ^ 6 = 64`
dimensional space of computational basis states.  The normalisation factor is
`1 / √64 = 1 / 8`. -/
noncomputable def qft6 : Matrix (Fin 64) (Fin 64) ℂ := fun j k =>
  (1 / 8 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / 64)

/-- Complex conjugation of a `64`-th root of unity of the shape used in `qft6`. -/
lemma conj_qft_exp (a b : ℕ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (a * b) / 64))
      = Complex.exp (-(2 * Real.pi * Complex.I * (a * b) / 64)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal,
    Complex.conj_natCast]
  ring

/-- The `64`-th root of unity attached to a difference of indices. -/
noncomputable def zeta (d : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * d / 64)

lemma zeta_pow_64 (d : ℤ) : zeta d ^ 64 = 1 := by
  have : ((64 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * d / 64) = (d : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [zeta, ← Complex.exp_nat_mul, this, Complex.exp_int_mul_two_pi_mul_I]

lemma zeta_ne_one {j l : Fin 64} (h : j ≠ l) : zeta ((j : ℕ) - (l : ℕ) : ℂ) ≠ 1 := by
  intro hz
  rw [zeta, Complex.exp_eq_one_iff] at hz
  obtain ⟨n, hn⟩ := hz
  have hd : ((j : ℕ) : ℂ) - (l : ℕ) = (n : ℂ) * 64 := by
    field_simp at hn
    linear_combination hn
  have hd' : ((j : ℕ) : ℤ) - (l : ℕ) = n * 64 := by exact_mod_cast hd
  have hj := j.isLt
  have hl := l.isLt
  have : (j : ℕ) = (l : ℕ) := by omega
  exact h (Fin.ext this)

/-- The 6-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_6 : qft6 ∈ Matrix.unitaryGroup (Fin 64) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin 64, qft6 j k * (star qft6) k l
      = (1 / 64 : ℂ) * zeta (((j : ℕ) : ℂ) - (l : ℕ)) ^ (k : ℕ) := by
    intro k
    have hc : (star qft6) k l
        = (1 / 8 : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ((l : ℕ) * (k : ℕ)) / 64)) := by
      rw [Matrix.star_apply]
      simp only [qft6, RCLike.star_def, map_mul, map_div₀, map_one, map_ofNat, conj_qft_exp]
    rw [hc]
    simp only [qft6]
    rw [show (1 / 8 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / 64) *
        ((1 / 8 : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ((l : ℕ) * (k : ℕ)) / 64)))
        = (1 / 64 : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / 64) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((l : ℕ) * (k : ℕ)) / 64))) by ring]
    rw [zeta, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Fin.sum_univ_eq_sum_range (fun k => (1 / 64 : ℂ) * zeta (((j : ℕ) : ℂ) - (l : ℕ)) ^ k) 64]
  rw [← Finset.mul_sum]
  by_cases h : j = l
  · subst h
    simp [zeta]
  · rw [if_neg h]
    rw [geom_sum_eq (zeta_ne_one h) 64]
    have h64 : zeta (((j : ℕ) : ℂ) - (l : ℕ)) ^ 64 = 1 := by
      have := zeta_pow_64 ((j : ℤ) - (l : ℤ))
      simpa using this
    rw [h64]
    simp

end QC

