import Mathlib
/-!
# Batch 11 — Fibonacci-anyon extras (F-matrix, fusion, golden identities). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
-- `Real` is opened so that `goldenRatio` refers to `Real.goldenRatio`
-- (`gold_sq` is the deprecated alias of `Real.goldenRatio_sq`).
open Matrix Real
noncomputable def Fmat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![goldenRatio⁻¹, Real.sqrt goldenRatio⁻¹; Real.sqrt goldenRatio⁻¹, -goldenRatio⁻¹]
/-- Fibonacci fusion matrix N_τ. -/
def Nfus : Matrix (Fin 2) (Fin 2) ℝ := !![0,1; 1,1]

theorem F_symmetric : Fmatᵀ = Fmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := Real.goldenRatio_sq

theorem golden_inv : goldenRatio⁻¹ = goldenRatio - 1 :=
  inv_eq_of_mul_eq_one_right (by nlinarith [golden_sq])

/-- The key scalar identity behind unitarity: `φ⁻¹ ^ 2 + φ⁻¹ = 1`. -/
private lemma golden_inv_sq_add : goldenRatio⁻¹ ^ 2 + goldenRatio⁻¹ = 1 := by
  rw [golden_inv]; nlinarith [golden_sq]

theorem F_unitary : Fmat * Fmatᴴ = 1 := by
  have hs : Real.sqrt goldenRatio⁻¹ ^ 2 = goldenRatio⁻¹ := Real.sq_sqrt (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fmat, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
      Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.one_apply_eq,
      Fin.mk_zero, Fin.mk_one] <;>
    first
      | nlinarith [golden_inv_sq_add, hs]
      | (rw [Matrix.one_apply_ne (by decide)]; ring)

theorem F_det : Fmat.det = -1 := by
  have hs : Real.sqrt goldenRatio⁻¹ ^ 2 = goldenRatio⁻¹ := Real.sq_sqrt (by positivity)
  rw [Matrix.det_fin_two]
  simp only [Fmat, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  nlinarith [golden_inv_sq_add, hs]

theorem fusion_det : Nfus.det = -1 := by
  rw [Matrix.det_fin_two]
  simp [Nfus]

theorem fusion_trace : Matrix.trace Nfus = 1 := by
  simp [Nfus, Matrix.trace_fin_two]
end BrockianQuantum

