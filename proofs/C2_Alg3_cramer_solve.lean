import Mathlib
namespace C2.Alg3

/-- Cramer-style solution: if `det A` is a unit, then `A⁻¹ b` solves `A x = b`. -/
theorem cramer_solve {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ) :
    A.mulVec (A⁻¹.mulVec b) = b := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]

/-- The adjugate identity `A * adj A = det A • 1`. -/
theorem adjugate_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : A * A.adjugate = A.det • 1 :=
  Matrix.mul_adjugate A

/-- Sylow's existence theorem: a finite group has a Sylow `p`-subgroup. -/
theorem sylow_exists {G : Type*} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    ∃ _P : Sylow p G, True :=
  ⟨Nonempty.some inferInstance, trivial⟩

end C2.Alg3

