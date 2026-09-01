import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped Real

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace Chem

open Matrix

/-- The Hückel (adjacency) matrix of the cycle graph `C₄`, over `ℝ`. -/
noncomputable def C4Matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  (SimpleGraph.cycleGraph 4).adjMatrix ℝ

lemma C4Matrix_eq : C4Matrix = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C4Matrix, SimpleGraph.adjMatrix, SimpleGraph.cycleGraph] <;> decide

/-- The characteristic determinant of `C₄`. -/
lemma det_C4_sub (mu : ℝ) :
    (C4Matrix - mu • (1 : Matrix (Fin 4) (Fin 4) ℝ)).det = mu ^ 4 - 4 * mu ^ 2 := by
  have hmat : C4Matrix - mu • (1 : Matrix (Fin 4) (Fin 4) ℝ) =
      !![-mu, 1, 0, 1; 1, -mu, 1, 0; 0, 1, -mu, 1; 1, 0, 1, -mu] := by
    rw [C4Matrix_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hmat]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [show (Fin.succAbove (1 : Fin 4) (2 : Fin 3)) = 3 from by decide,
    show (Fin.succAbove (3 : Fin 4) (2 : Fin 3)) = 2 from by decide,
    Matrix.cons_val_three, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- `mu` is an eigenvalue of the `C₄` adjacency matrix iff it is a root of `x⁴ - 4x²`. -/
lemma isEigenvalue_iff (mu : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4Matrix *ᵥ v = mu • v) ↔ mu ^ 4 - 4 * mu ^ 2 = 0 := by
  have hv : ∀ v : Fin 4 → ℝ,
      (C4Matrix *ᵥ v = mu • v) ↔ (C4Matrix - mu • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ v = 0 := by
    intro v
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec]
  calc (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4Matrix *ᵥ v = mu • v)
      ↔ (∃ v : Fin 4 → ℝ, v ≠ 0 ∧
          (C4Matrix - mu • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ v = 0) := by
        exact exists_congr fun v => and_congr_right fun _ => hv v
    _ ↔ (C4Matrix - mu • (1 : Matrix (Fin 4) (Fin 4) ℝ)).det = 0 :=
        Matrix.exists_mulVec_eq_zero_iff
    _ ↔ mu ^ 4 - 4 * mu ^ 2 = 0 := by rw [det_C4_sub]

/-- The values `2 cos (2πk/4)` for `k = 0,1,2,3` are exactly `2, 0, -2, 0`. -/
lemma cos_values_iff (mu : ℝ) :
    (∃ k : Fin 4, mu = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 4)) ↔
      (mu = 2 ∨ mu = 0 ∨ mu = -2) := by
  have h1 : 2 * Real.pi * (1 : ℕ) / 4 = Real.pi / 2 := by push_cast; ring
  have h2 : 2 * Real.pi * (2 : ℕ) / 4 = Real.pi := by push_cast; ring
  have h3 : 2 * Real.pi * (3 : ℕ) / 4 = Real.pi + Real.pi / 2 := by push_cast; ring
  have hc3 : Real.cos (2 * Real.pi * (3 : ℕ) / 4) = 0 := by
    rw [h3, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi]
    ring
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; norm_num
    · right; left; rw [h1, Real.cos_pi_div_two]; ring
    · right; right; rw [h2, Real.cos_pi]; ring
    · right; left; rw [hc3]; ring
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · refine ⟨1, ?_⟩
      rw [show ((1 : Fin 4) : ℕ) = 1 from rfl, h1, Real.cos_pi_div_two]; ring
    · refine ⟨2, ?_⟩
      rw [show ((2 : Fin 4) : ℕ) = 2 from rfl, h2, Real.cos_pi]; ring

/-- **Hückel theory for cyclobutadiene (C₄).**
A real number `mu` is an eigenvalue of the adjacency (Hückel) matrix of the cycle graph `C₄`
if and only if `mu = 2 cos (2πk/4)` for some `k ∈ {0,1,2,3}`. -/
theorem huckel_C4 (mu : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4Matrix *ᵥ v = mu • v) ↔
      ∃ k : Fin 4, mu = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) := by
  rw [isEigenvalue_iff, cos_values_iff]
  constructor
  · intro h
    have h' : mu ^ 2 * ((mu - 2) * (mu + 2)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h1 | h1
    · right; left; exact pow_eq_zero_iff (by norm_num) |>.1 h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · left; linarith
      · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num

end Chem

