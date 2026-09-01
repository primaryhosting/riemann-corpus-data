import Mathlib
namespace Frontier.BrockianNextLevel
theorem excluded_residue_count (q : ℕ) [NeZero q] (g : ZMod q) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod q => r = 0 ∨ r = -g)).card = 2 := by
  have h : (Finset.univ.filter (fun r : ZMod q => r = 0 ∨ r = -g)) = {0, -g} := by
    ext r; simp [Finset.mem_insert]
  rw [h, Finset.card_insert_of_notMem (by simpa using hg), Finset.card_singleton]
theorem pentagon_trace_zero :
    Matrix.trace (!![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_succ]
theorem golden_fixed_point : ((1 + Real.sqrt 5)/2)^2 = ((1 + Real.sqrt 5)/2) + 1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h]
end Frontier.BrockianNextLevel

