import Mathlib
namespace C3.BD5

/-- The dihedral group of order 10 (symmetries of the regular pentagon) has 10 elements. -/
theorem dihedral5_card : Nat.card (DihedralGroup 5) = 10 := by
  simp [Nat.card_eq_fintype_card, DihedralGroup.card]

/-- The golden ratio satisfies `φ² = φ + 1`. -/
theorem golden_pow2 : ((1+Real.sqrt 5)/2)^2 = ((1+Real.sqrt 5)/2)+1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

/-- The golden ratio satisfies `φ³ = 2φ + 1`. -/
theorem golden_pow3 : ((1+Real.sqrt 5)/2)^3 = 2*((1+Real.sqrt 5)/2)+1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h, Real.sqrt_nonneg 5]

/-- `cos (π/5) = (1 + √5)/4`, i.e. half the golden ratio. -/
theorem cos_pi5_val : Real.cos (Real.pi/5) = (1+Real.sqrt 5)/4 := Real.cos_pi_div_five

end C3.BD5

