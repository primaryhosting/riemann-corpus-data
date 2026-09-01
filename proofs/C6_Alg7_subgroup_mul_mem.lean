import Mathlib
namespace C6.Alg7

theorem subgroup_mul_mem {G : Type*} [Group G] (H : Subgroup G) (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a*b ∈ H :=
  H.mul_mem ha hb

theorem inv_inv_group {G : Type*} [Group G] (a : G) : a⁻¹⁻¹ = a :=
  inv_inv a

theorem det_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : (c • A).det = c^n * A.det := by
  simp

end C6.Alg7

