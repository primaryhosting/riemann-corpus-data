/-
# Hankel Christoffel 13 18
Category: B Christoffel
Target: Zeta23Scaffold.hankel_christoffel_13_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The 3×3 rational Hankel (moment) matrix `(m_{i+j})_{0 ≤ i,j ≤ 2}` of the
sine-kernel moment sequence `m_0, …, m_4 = 1, 1, 4/3, 2, 13/4` at `λ = 1`. -/
def hankelM : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The Christoffel value `Λ₂(0;1)`, computed as the Hankel determinant ratio
`det M / det M'`, where `M'` is the lower-right 2×2 Hankel minor. -/
def hankelLambda : ℚ := hankelM.det / (Matrix.det !![(4:ℚ)/3, 2; 2, 13/4])

/-- The exact-arithmetic core of the conditional `13/18` rung:
(a) `det M = 5/108`; (b) `Λ = 5/36`; (c) `1 - Λ = 31/36`; (d) `2(1 - Λ) - 1 = 13/18`. -/
theorem hankel_christoffel_13_18 :
    hankelM.det = 5/108 ∧ hankelLambda = 5/36 ∧ 1 - hankelLambda = 31/36 ∧
      2 * (1 - hankelLambda) - 1 = 13/18 := by
  have hdet : hankelM.det = 5/108 := by
    simp [hankelM, Matrix.det_fin_three]
    norm_num
  have hlam : hankelLambda = 5/36 := by
    rw [hankelLambda, hdet, Matrix.det_fin_two_of]
    norm_num
  refine ⟨hdet, hlam, by rw [hlam]; norm_num, by rw [hlam]; norm_num⟩

end Zeta23Scaffold

