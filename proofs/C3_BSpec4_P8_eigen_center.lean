import Mathlib
open Matrix Polynomial
namespace C3.BSpec4
def P8 : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of (fun i j => if i=j then 2 else if (i:ℤ)-(j:ℤ)=1 ∨ (j:ℤ)-(i:ℤ)=1 then -1 else 0)

/-- The eigenvector of `P8` for the eigenvalue `2 - 2 cos (π/9)`:
its `i`-th entry is `sin ((i+1) π/9)`. -/
noncomputable def eigvec8 : Fin 8 → ℝ := fun i => Real.sin (((i : ℝ) + 1) * (Real.pi / 9))

/-- Three-term recurrence satisfied by `t ↦ sin t` with step `π/9`. -/
private lemma sin_three_term (a : ℝ) :
    Real.sin (a - Real.pi / 9) - Real.cos (Real.pi / 9) * Real.sin a * 2
      + Real.sin (a + Real.pi / 9) = 0 := by
  rw [Real.sin_add, Real.sin_sub]; ring

private lemma P8_mulVec_eigvec8 :
    ((Matrix.scalar (Fin 8)) (2 - 2 * Real.cos (Real.pi / 9)) - P8).mulVec eigvec8 = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_eight, P8, eigvec8, Matrix.scalar_apply,
      Matrix.diagonal]
  all_goals try ring_nf
  · have h := sin_three_term (Real.pi * (1 / 9))
    rw [show Real.pi * (1 / 9) - Real.pi / 9 = 0 by ring, Real.sin_zero] at h
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (2 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (3 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (4 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (5 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (6 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (7 / 9))
    ring_nf at h
    linarith
  · have h := sin_three_term (Real.pi * (8 / 9))
    rw [show Real.pi * (8 / 9) + Real.pi / 9 = Real.pi by ring, Real.sin_pi] at h
    ring_nf at h
    linarith

private lemma eigvec8_ne_zero : eigvec8 ≠ 0 := by
  intro h
  have h0 : eigvec8 0 = 0 := by rw [h]; rfl
  have hpos : 0 < Real.sin (Real.pi / 9) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by nlinarith [Real.pi_pos])
  simp only [eigvec8] at h0
  norm_num at h0
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

theorem P8_eigen_center : P8.charpoly.eval (2 - 2*Real.cos (Real.pi/9)) = 0 := by
  rw [Matrix.eval_charpoly]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨eigvec8, eigvec8_ne_zero, P8_mulVec_eigvec8⟩

theorem P8_symm : P8.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, P8, Matrix.of_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    congr 1
    exact propext or_comm

theorem C6_trace : Matrix.trace (!![0,1,0,0,0,1;1,0,1,0,0,0;0,1,0,1,0,0;0,0,1,0,1,0;0,0,0,1,0,1;1,0,0,0,1,0] : Matrix (Fin 6) (Fin 6) ℝ) = 0 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_six]
end C3.BSpec4

