import Mathlib
/-!
# Batch 6 — GHZ / W three-qubit states and their stabilizers. All TRUE; bare `import Mathlib`.
Basis |b0 b1 b2> indexed 0..7. XXX = X⊗X⊗X (anti-diagonal, i+j=7). Z-stabilizers are diagonal
with signs (-1)^(sum of the two Z-bits).
-/
namespace BrockianQuantum
open Matrix
noncomputable def c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
noncomputable def dd : ℂ := (Real.sqrt 3 : ℂ)⁻¹
def XXX : Matrix (Fin 8) (Fin 8) ℂ := fun i j => if (i : ℕ) + (j : ℕ) = 7 then 1 else 0
def ZZI : Matrix (Fin 8) (Fin 8) ℂ := Matrix.diagonal ![1,1,-1,-1,-1,-1,1,1]
def ZIZ : Matrix (Fin 8) (Fin 8) ℂ := Matrix.diagonal ![1,-1,1,-1,-1,1,-1,1]
def IZZ : Matrix (Fin 8) (Fin 8) ℂ := Matrix.diagonal ![1,-1,-1,1,1,-1,-1,1]
noncomputable def GHZ : Fin 8 → ℂ := ![c,0,0,0,0,0,0,c]
noncomputable def Wst : Fin 8 → ℂ := ![0,dd,dd,0,dd,0,0,0]

/-- `|c|² = 1/2`. -/
theorem normSq_c : Complex.normSq c = 1/2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [c, ← Complex.ofReal_inv, Complex.normSq_ofReal, ← mul_inv, h]
  norm_num

/-- `|dd|² = 1/3`. -/
theorem normSq_dd : Complex.normSq dd = 1/3 := by
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [dd, ← Complex.ofReal_inv, Complex.normSq_ofReal, ← mul_inv, h]
  norm_num

theorem GHZ_XXX_eigen : XXX.mulVec GHZ = GHZ := by
  funext i
  fin_cases i <;>
    simp [XXX, GHZ, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

theorem GHZ_ZZI_eigen : ZZI.mulVec GHZ = GHZ := by
  funext i
  fin_cases i <;> simp [ZZI, GHZ, Matrix.mulVec_diagonal]

theorem GHZ_ZIZ_eigen : ZIZ.mulVec GHZ = GHZ := by
  funext i
  fin_cases i <;> simp [ZIZ, GHZ, Matrix.mulVec_diagonal]

theorem GHZ_IZZ_eigen : IZZ.mulVec GHZ = GHZ := by
  funext i
  fin_cases i <;> simp [IZZ, GHZ, Matrix.mulVec_diagonal]

theorem GHZ_normalized : ∑ i, Complex.normSq (GHZ i) = 1 := by
  simp [GHZ, Fin.sum_univ_eight, normSq_c]
  norm_num

theorem W_normalized : ∑ i, Complex.normSq (Wst i) = 1 := by
  simp [Wst, Fin.sum_univ_eight, normSq_dd]
  norm_num

theorem GHZ_W_orthogonal : ∑ i, (starRingEnd ℂ) (GHZ i) * Wst i = 0 := by
  simp [GHZ, Wst, Fin.sum_univ_eight]
end BrockianQuantum

