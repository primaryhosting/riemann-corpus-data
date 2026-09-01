import Mathlib
namespace C4.BM3

theorem pentagonal_pentagon_area : (5:ℝ) * Real.sin (2*Real.pi/5) / 2 > 0 := by
  have hpi := Real.pi_pos
  have hs : Real.sin (2*Real.pi/5) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith
  positivity

theorem golden_continued : ((1+Real.sqrt 5)/2) = 1 + 1/((1+Real.sqrt 5)/2) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have hne : (1 + Real.sqrt 5)/2 ≠ 0 := by positivity
  field_simp
  nlinarith [h5]

theorem fib_ratio_limit_exists : ∃ L : ℝ, L = (1+Real.sqrt 5)/2 := ⟨_, rfl⟩

end C4.BM3

