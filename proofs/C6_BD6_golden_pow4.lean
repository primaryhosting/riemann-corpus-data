import Mathlib
namespace C6.BD6

/-- `Real.sqrt 5` squared is `5`. -/
private lemma sq_sqrt_five : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem golden_pow4 : ((1+Real.sqrt 5)/2)^4 = 3*((1+Real.sqrt 5)/2) + 2 := by
  linear_combination ((Real.sqrt 5 ^ 2 + 4 * Real.sqrt 5 + 11) / 16) * sq_sqrt_five

theorem golden_pow5 : ((1+Real.sqrt 5)/2)^5 = 5*((1+Real.sqrt 5)/2) + 3 := by
  linear_combination
    ((Real.sqrt 5 ^ 3 + 5 * Real.sqrt 5 ^ 2 + 15 * Real.sqrt 5 + 35) / 32) * sq_sqrt_five

theorem lucas_golden : ((1+Real.sqrt 5)/2)^3 + ((1-Real.sqrt 5)/2)^3 = 4 := by
  linear_combination (3/4 : ℝ) * sq_sqrt_five

end C6.BD6

