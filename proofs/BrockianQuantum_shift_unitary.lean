import Mathlib
/-!
# Stabilizer formalism: qudit generalized-Pauli unitarity + qubit Pauli anticommutation.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. All TRUE.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** (generalized Pauli X). -/
def shift : Matrix (ZMod d) (ZMod d) ℂ := fun i j => if i = j + 1 then 1 else 0

/-- Qudit **clock** (generalized Pauli Z), `ω = exp(2πi/d)`. -/
noncomputable def clock : Matrix (ZMod d) (ZMod d) ℂ :=
  fun i j => if i = j then Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) else 0

/-- The shift gate is **unitary**: `X * Xᴴ = 1` (it is a permutation matrix). -/
theorem shift_unitary : shift d * (shift d)ᴴ = 1 := by
  ext i l
  -- `i = x + 1` is the same condition as `x = i - 1`, which lets us evaluate the sum.
  have key : ∀ x : ZMod d, (i = x + 1) = (x = i - 1) := by
    intro x; simp [eq_sub_iff_add_eq, eq_comm]
  have key2 : ∀ x : ZMod d, (l = x + 1) = (x = l - 1) := by
    intro x; simp [eq_sub_iff_add_eq, eq_comm]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, shift, Matrix.one_apply,
    RCLike.star_def, key, key2, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (i - 1)]
  simp [sub_left_inj]

/-- The clock gate is **unitary**: `Z * Zᴴ = 1` (diagonal of unit-modulus phases). -/
theorem clock_unitary : clock d * (clock d)ᴴ = 1 := by
  have hconj : ∀ z : ℂ, (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * z / d)
      = -(2 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) z / d) := by
    intro z
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      Complex.conj_natCast]
    ring
  ext i l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, clock, Matrix.one_apply,
    RCLike.star_def, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = l
    · subst h
      simp only [if_true]
      -- `exp z * conj (exp z) = exp z * exp (-z) = 1` since the exponent is purely imaginary.
      rw [← Complex.exp_conj, hconj, Complex.conj_natCast, Complex.exp_neg,
        mul_inv_cancel₀ (Complex.exp_ne_zero _)]
    · simp [h, Ne.symm h]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- **Qubit Pauli anticommutation** (base case of the stabilizer group): `X Z = − Z X` for the
2×2 Pauli matrices `X = [[0,1],[1,0]]`, `Z = [[1,0],[0,-1]]`. -/
theorem pauli_anticommute :
    (Matrix.of ![![(0:ℂ), 1], ![1, 0]]) * (Matrix.of ![![(1:ℂ), 0], ![0, -1]])
      = - ((Matrix.of ![![(1:ℂ), 0], ![0, -1]]) * (Matrix.of ![![(0:ℂ), 1], ![1, 0]])) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

end BrockianQuantum

