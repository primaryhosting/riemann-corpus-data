import Mathlib
open Matrix Polynomial
namespace C5.BSp6
def P10 : Matrix (Fin 10) (Fin 10) ℝ := Matrix.of (fun i j => if i=j then 2 else if (i:ℤ)-(j:ℤ)=1 ∨ (j:ℤ)-(i:ℤ)=1 then -1 else 0)

theorem P10_symm : P10.IsSymm := by
  ext i j
  simp only [P10, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases h2 : (i:ℤ)-(j:ℤ)=1 ∨ (j:ℤ)-(i:ℤ)=1
    · rw [if_pos h2, if_pos h2.symm]
    · rw [if_neg h2, if_neg (fun h3 => h2 h3.symm)]

/-- The eigenvector of `P10` for the eigenvalue `2 - 2 cos (π/11)`:
its `i`-th entry is `sin ((i+1) π / 11)`. -/
noncomputable def v10 : Fin 10 → ℝ := fun i => Real.sin (((i : ℕ) + 1) * (Real.pi / 11))

/-- The three-term recurrence `sin(aθ) + sin((a+2)θ) = 2 cos θ · sin((a+1)θ)` for `θ = π/11`. -/
lemma sin_three_term (a : ℝ) :
    Real.sin (a * (Real.pi / 11)) + Real.sin ((a + 2) * (Real.pi / 11))
      = 2 * Real.cos (Real.pi / 11) * Real.sin ((a + 1) * (Real.pi / 11)) := by
  have h1 : a * (Real.pi / 11) = (a + 1) * (Real.pi / 11) - (Real.pi / 11) := by ring
  have h2 : (a + 2) * (Real.pi / 11) = (a + 1) * (Real.pi / 11) + (Real.pi / 11) := by ring
  rw [h1, h2, Real.sin_sub, Real.sin_add]; ring

lemma sin_eleven : Real.sin (11 * (Real.pi / 11)) = 0 := by
  have h : (11 : ℝ) * (Real.pi / 11) = Real.pi := by ring
  rw [h, Real.sin_pi]

lemma v10_ne_zero : v10 ≠ 0 := by
  intro h
  have h0 : v10 0 = 0 := by rw [h]; rfl
  simp only [v10] at h0
  norm_num at h0
  have hpos : 0 < Real.sin (Real.pi / 11) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [Real.pi_pos]
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- `v10` lies in the kernel of `(2 - 2 cos (π/11)) • I - P10`. -/
lemma mulVec_eq_zero :
    ((Matrix.scalar (Fin 10) (2 - 2 * Real.cos (Real.pi / 11))) - P10) *ᵥ v10 = 0 := by
  have k0 := sin_three_term 0
  have k1 := sin_three_term 1
  have k2 := sin_three_term 2
  have k3 := sin_three_term 3
  have k4 := sin_three_term 4
  have k5 := sin_three_term 5
  have k6 := sin_three_term 6
  have k7 := sin_three_term 7
  have k8 := sin_three_term 8
  have k9 := sin_three_term 9
  have h11 := sin_eleven
  norm_num [Real.sin_zero] at k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
  rw [h11] at k9
  funext i
  fin_cases i <;>
  · simp only [Matrix.mulVec, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      dotProduct, P10, Matrix.of_apply, v10, Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.zero_apply,
      Fin.val_succ, Fin.ext_iff, Fin.val_zero]
    norm_num
    linarith

theorem P10_eigen : P10.charpoly.eval (2 - 2*Real.cos (Real.pi/11)) = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨v10, v10_ne_zero, mulVec_eq_zero⟩

theorem golden_sqrt5 : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
end C5.BSp6

