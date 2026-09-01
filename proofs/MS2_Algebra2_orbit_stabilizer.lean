import Mathlib
namespace MS2.Algebra2
theorem orbit_stabilizer {G α : Type*} [Group G] [MulAction G α] [Fintype G] (a : α) [Fintype (MulAction.orbit G a)] [Fintype (MulAction.stabilizer G a)] :
    Fintype.card (MulAction.orbit G a) * Fintype.card (MulAction.stabilizer G a) = Fintype.card G :=
  MulAction.card_orbit_mul_card_stabilizer_eq_card_group G a
theorem det_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : (A*B).det = A.det * B.det :=
  Matrix.det_mul A B
theorem rank_nullity {V W : Type*} [Field ℝ] [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] W) :
    Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker f) = Module.finrank ℝ V :=
  LinearMap.finrank_range_add_finrank_ker f
/-- The Vandermonde determinant. The only change to the original statement is the explicit
type ascription `(i j : Fin n)` on the matrix entries: without it, the second index was
inferred to be a natural number and the expression was not a square matrix. -/
theorem vandermonde_det {n : ℕ} (v : Fin n → ℝ) :
    (Matrix.of (fun (i j : Fin n) => (v i)^(j:ℕ))).det
      = ∏ i ∈ Finset.univ, ∏ j ∈ Finset.univ.filter (· > i), (v j - v i) := by
  have hfil : ∀ i : Fin n, Finset.univ.filter (· > i) = Finset.Ioi i := by
    intro i; ext j; simp
  simp only [hfil]
  exact Matrix.det_vandermonde v
theorem first_iso {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty ((G ⧸ f.ker) ≃* f.range) :=
  ⟨QuotientGroup.quotientKerEquivRange f⟩
end MS2.Algebra2

