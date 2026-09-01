import Mathlib
/-!
# Batch 13 — Clifford conjugations (H, S normalize the Pauli group). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
noncomputable def hc : ℂ := (Real.sqrt 2 : ℂ)⁻¹
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := !![hc, hc; hc, -hc]
noncomputable def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]
def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
noncomputable def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem S_Z_commute : S * PZ = PZ * S := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S, PZ]

theorem S_conj_Y : S * PY * Sᴴ = -PX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S, PY, PX, Matrix.conjTranspose_apply]

theorem S_conj_Z : S * PZ * Sᴴ = PZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S, PZ, Matrix.conjTranspose_apply]

theorem HS_conj_X : (H * S) * PX * (H * S)ᴴ = -PY := by
  have hcs : hc ^ 2 = 1 / 2 := by
    have h2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [hc, inv_pow, ← Complex.ofReal_pow, h2]
    norm_num
  have hconj : (starRingEnd ℂ) hc = hc := by rw [hc]; simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S, H, PX, PY, Matrix.conjTranspose_apply,
      hconj] <;> ring_nf
  all_goals simp only [hcs]
  all_goals ring_nf

theorem HS_conj_Z : (H * S) * PZ * (H * S)ᴴ = PX := by
  have hcs : hc ^ 2 = 1 / 2 := by
    have h2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [hc, inv_pow, ← Complex.ofReal_pow, h2]
    norm_num
  have hconj : (starRingEnd ℂ) hc = hc := by rw [hc]; simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S, H, PZ, PX, Matrix.conjTranspose_apply,
      hconj] <;> ring_nf
  all_goals simp only [hcs, Complex.I_sq]
  all_goals ring_nf

theorem H_conj_Y : H * PY * Hᴴ = -PY := by
  have hcs : hc ^ 2 = 1 / 2 := by
    have h2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [hc, inv_pow, ← Complex.ofReal_pow, h2]
    norm_num
  have hconj : (starRingEnd ℂ) hc = hc := by rw [hc]; simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, H, PY, Matrix.conjTranspose_apply, hconj] <;>
    ring_nf
  all_goals simp only [hcs]
  all_goals ring_nf

theorem S_unitary_left : Sᴴ * S = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S, Matrix.conjTranspose_apply]

end BrockianQuantum

