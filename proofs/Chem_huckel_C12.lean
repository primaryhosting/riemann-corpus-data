import Mathlib
/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

/-- Adjacency matrix of the cycle graph `C₁₂` (the Hückel matrix of the 12-membered
annulene, with `α = 0`, `β = 1`): vertices `i` and `j` are adjacent iff they are
consecutive modulo `12`. -/
def C12 : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i j => if (i.val + 1) % 12 = j.val ∨ (j.val + 1) % 12 = i.val then 1 else 0

/-- The Hückel eigenvalues `2 cos (2πk/12)`. -/
noncomputable def hval (k : Fin 12) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ)

/-- The DFT (Vandermonde) matrix, whose `k`-th column is the eigenvector belonging to
the eigenvalue `hval k`. -/
noncomputable def V12 : Matrix (Fin 12) (Fin 12) ℂ :=
  Matrix.vandermonde (fun i : Fin 12 => om ^ (i : ℕ))

/-- `C12` really is the adjacency matrix of Mathlib's cycle graph on `Fin 12`. -/
lemma C12_eq_adjMatrix : C12 = (SimpleGraph.cycleGraph 12).adjMatrix ℂ := by
  ext i j
  have h : ((i.val + 1) % 12 = j.val ∨ (j.val + 1) % 12 = i.val)
      ↔ (SimpleGraph.cycleGraph 12).Adj i j := by
    revert i j; decide
  simp [C12, SimpleGraph.adjMatrix_apply, ← h]

lemma om_prim : IsPrimitiveRoot om 12 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 12 (by norm_num)

lemma om_pow_twelve : om ^ 12 = 1 := om_prim.pow_eq_one

lemma hval_eq (k : Fin 12) : hval k = om ^ (k : ℕ) + (om ^ (k : ℕ))⁻¹ := by
  have h1 : om ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 12 : ℝ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hval, h1, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

lemma V12_apply (i k : Fin 12) : V12 i k = (om ^ (k : ℕ)) ^ (i : ℕ) := by
  simp [V12, Matrix.vandermonde, ← pow_mul, Nat.mul_comm]

/-- The row-`i` recursion for the cycle: `u^{i-1} + u^{i+1} = u^i (u + u^{-1})`, written with
`u^11` in place of `u⁻¹` using `u^12 = 1`. -/
lemma sum_C12_pow (i : Fin 12) (u : ℂ) (hu : u ^ 12 = 1) :
    ∑ j : Fin 12, C12 i j * u ^ (j : ℕ) = u ^ (i : ℕ) * (u + u ^ 11) := by
  fin_cases i <;>
    simp [C12, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination (-1 : ℂ) * hu
      | linear_combination (-u) * hu
      | linear_combination (-u ^ 2) * hu
      | linear_combination (-u ^ 3) * hu
      | linear_combination (-u ^ 4) * hu
      | linear_combination (-u ^ 5) * hu
      | linear_combination (-u ^ 6) * hu
      | linear_combination (-u ^ 7) * hu
      | linear_combination (-u ^ 8) * hu
      | linear_combination (-u ^ 9) * hu
      | linear_combination (-(1 + u ^ 10)) * hu

lemma comm_key : C12 * V12 = V12 * Matrix.diagonal hval := by
  ext i k
  have hu : (om ^ (k : ℕ)) ^ 12 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, om_pow_twelve, one_pow]
  have hinv : (om ^ (k : ℕ))⁻¹ = (om ^ (k : ℕ)) ^ 11 :=
    inv_eq_of_mul_eq_one_right (by linear_combination hu)
  rw [Matrix.mul_apply, Matrix.mul_diagonal, hval_eq, hinv, V12_apply]
  simp only [V12_apply]
  exact sum_C12_pow i _ hu

lemma det_V12_ne_zero : (V12).det ≠ 0 := by
  rw [V12, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [sub_ne_zero]
  intro hzero
  have heq := om_prim.pow_inj j.isLt i.isLt hzero
  have hlt : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp (Finset.mem_Ioi.mp hj)
  omega

lemma det_sub_smul (μ : ℂ) :
    (C12 - μ • (1 : Matrix (Fin 12) (Fin 12) ℂ)).det = ∏ k : Fin 12, (hval k - μ) := by
  have hdiag : Matrix.diagonal (fun k => hval k - μ)
      = Matrix.diagonal hval - μ • (1 : Matrix (Fin 12) (Fin 12) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have key : (C12 - μ • (1 : Matrix (Fin 12) (Fin 12) ℂ)) * V12
      = V12 * Matrix.diagonal (fun k => hval k - μ) := by
    rw [hdiag, sub_mul, mul_sub, comm_key, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm (V12).det] at hdet
  exact mul_right_cancel₀ det_V12_ne_zero hdet

/-- **Hückel theory for the 12-membered cycle.**  A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph `C₁₂` if and only if `μ = 2 cos (2πk/12)` for some
`k = 0, …, 11`. -/
theorem huckel_C12 (μ : ℂ) :
    (∃ v : Fin 12 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 12).adjMatrix ℂ *ᵥ v = μ • v) ↔
      ∃ k : Fin 12, μ = ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ) := by
  rw [← C12_eq_adjMatrix]
  have step1 : (∃ v : Fin 12 → ℂ, v ≠ 0 ∧ C12 *ᵥ v = μ • v) ↔
      ∃ v : Fin 12 → ℂ, v ≠ 0 ∧ (C12 - μ • (1 : Matrix (Fin 12) (Fin 12) ℂ)) *ᵥ v = 0 := by
    refine exists_congr fun v => and_congr_right fun _ => ?_
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [step1, Matrix.exists_mulVec_eq_zero_iff, det_sub_smul, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, by rw [sub_eq_zero] at hk; rw [← hk, hval]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, by rw [hval, ← hk, sub_self]⟩

end Chem

