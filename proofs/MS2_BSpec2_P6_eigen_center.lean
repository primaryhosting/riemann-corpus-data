import Mathlib
open Matrix Polynomial
namespace MS2.BSpec2
def C7 : Matrix (Fin 7) (Fin 7) ℝ := Matrix.of (fun i j => if (i-j = 1 ∨ j-i = 1 ∨ (i=0∧j=6) ∨ (i=6∧j=0)) then 1 else 0)
def P6 : Matrix (Fin 6) (Fin 6) ℝ := !![2,-1,0,0,0,0; -1,2,-1,0,0,0; 0,-1,2,-1,0,0; 0,0,-1,2,-1,0; 0,0,0,-1,2,-1; 0,0,0,0,-1,2]

/-- `2 - 2·cos(π/7)` is an eigenvalue of the path Laplacian-type matrix `P6`.
The witnessing eigenvector is `v i = sin((i+1)·π/7)`; the row identities follow from
`sin(x) + sin(x + 2t) = 2·cos t·sin(x + t)` together with `sin(7·π/7) = sin π = 0`. -/
theorem P6_eigen_center : P6.charpoly.eval (2 - 2*Real.cos (Real.pi/7)) = 0 := by
  set t : ℝ := Real.pi/7 with ht
  have K : ∀ x : ℝ, Real.sin x + Real.sin (x + 2*t) = 2 * Real.cos t * Real.sin (x + t) := by
    intro x
    simp only [Real.sin_add, Real.cos_add, two_mul]
    linear_combination (-Real.sin x) * (Real.sin_sq_add_cos_sq t)
  have h7 : Real.sin (7*t) = 0 := by
    rw [ht, show (7:ℝ) * (Real.pi/7) = Real.pi by ring, Real.sin_pi]
  have hst : Real.sin t ≠ 0 := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := t) (by rw [ht]; positivity)
      (by rw [ht]; linarith [Real.pi_pos])
    linarith
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun i => Real.sin ((i.val + 1) * t), ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    simp at h0
    exact hst h0
  · have K0 := K 0
    simp only [Real.sin_zero, zero_add] at K0
    have K1 := K t
    have K2 := K (2*t)
    have K3 := K (3*t)
    have K4 := K (4*t)
    have K5 := K (5*t)
    ring_nf at K0 K1 K2 K3 K4 K5 h7
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.scalar_apply, P6] <;>
      ring_nf <;> linarith

theorem C5_trace_zero : Matrix.trace (!![0,1,0,0,1;1,0,1,0,0;0,1,0,1,0;0,0,1,0,1;1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_succ]

/-- `2` is an eigenvalue of the 5-cycle adjacency matrix, witnessed by the all-ones vector. -/
theorem pentagon_eigen_two : (!![0,1,0,0,1;1,0,1,0,0;0,1,0,1,0;0,0,1,0,1;1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ).charpoly.eval 2 = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.scalar_apply] <;> ring

theorem P6_symmetric : P6.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P6]

theorem golden_sq : ((1+Real.sqrt 5)/2)^2 = ((1+Real.sqrt 5)/2)+1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h]
end MS2.BSpec2

