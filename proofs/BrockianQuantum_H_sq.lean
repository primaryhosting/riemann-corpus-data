import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix
noncomputable def hc : ℂ := (Real.sqrt 2 : ℂ)⁻¹
/-- Hadamard. -/ noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := !![hc, hc; hc, -hc]
def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
noncomputable def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `hc * hc = 1/2`, since `(√2)^2 = 2`. -/
private lemma hc_mul_hc : hc * hc = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hc, ← mul_inv, h2]
  norm_num

private lemma hc_sq : hc ^ 2 = 1 / 2 := by rw [pow_two, hc_mul_hc]

/-- `hc` is real, hence fixed by complex conjugation. -/
private lemma hc_conj : (starRingEnd ℂ) hc = hc := by
  simp [hc, ← Complex.ofReal_inv]

theorem H_sq : H * H = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, hc_mul_hc] <;> norm_num

theorem H_unitary : H * Hᴴ = 1 := by
  have hH : Hᴴ = H := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H, Matrix.conjTranspose_apply, hc_conj]
  rw [hH, H_sq]

theorem H_X_H : H * PX * H = PZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, PX, PZ, hc_mul_hc] <;> ring_nf

theorem H_Z_H : H * PZ * H = PX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, PX, PZ, hc_mul_hc] <;> ring_nf

theorem H_Y_H : H * PY * H = -PY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, PY] <;> ring_nf <;> simp [hc_sq] <;> ring_nf

theorem H_det : H.det = -1 := by
  rw [H, Matrix.det_fin_two_of]
  linear_combination -2 * hc_mul_hc

theorem H_eq_sum : H = hc • (PX + PZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, PX, PZ]
end BrockianQuantum

