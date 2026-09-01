import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 16-th root of unity. -/
noncomputable def zeta16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The adjacency matrix of the cycle graph `C₁₆` (Hückel matrix of an annulene
with 16 carbon atoms, in units where `α = 0` and `β = 1`).  Vertices are indexed
by `Fin 16` with addition modulo 16, and `i` is adjacent to `j` exactly when
`j = i + 1` or `i = j + 1`. -/
def C16adj : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ i = j + 1 then 1 else 0

/-- The predicted Hückel energy levels of `C₁₆`: `2 cos (2πk/16)`. -/
noncomputable def lam16 : Fin 16 → ℂ :=
  fun k => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 16) : ℝ) : ℂ)

/-- The Vandermonde matrix built from the 16-th roots of unity; its `k`-th column is
the eigenvector belonging to the `k`-th energy level. -/
noncomputable def V16 : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.vandermonde (fun j : Fin 16 => zeta16 ^ (j : ℕ))

lemma zeta16_pow16 : zeta16 ^ 16 = 1 := by
  rw [zeta16, ← Complex.exp_nat_mul]
  rw [show ((16 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 16) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma zeta16_pow_k_pow16 (k : ℕ) : (zeta16 ^ k) ^ 16 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta16_pow16, one_pow]

lemma zeta16_prim : IsPrimitiveRoot zeta16 16 := by
  have := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [zeta16] using this

/-- For any 16-th root of unity `z`, the geometric vector `i ↦ zⁱ` is an eigenvector of the
adjacency matrix of `C₁₆` with eigenvalue `z + z¹⁵ = z + z⁻¹`. -/
lemma C16adj_mulVec_geom (z : ℂ) (hz : z ^ 16 = 1) :
    C16adj *ᵥ (fun i : Fin 16 => z ^ (i : ℕ)) = (z + z ^ 15) • (fun i : Fin 16 => z ^ (i : ℕ)) := by
  funext i
  fin_cases i <;>
    simp [C16adj, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    (first
      | ring1
      | linear_combination (-(1 + z ^ 14)) * hz
      | linear_combination (-(1 : ℂ)) * hz
      | linear_combination (-z) * hz
      | linear_combination (-z ^ 2) * hz
      | linear_combination (-z ^ 3) * hz
      | linear_combination (-z ^ 4) * hz
      | linear_combination (-z ^ 5) * hz
      | linear_combination (-z ^ 6) * hz
      | linear_combination (-z ^ 7) * hz
      | linear_combination (-z ^ 8) * hz
      | linear_combination (-z ^ 9) * hz
      | linear_combination (-z ^ 10) * hz
      | linear_combination (-z ^ 11) * hz
      | linear_combination (-z ^ 12) * hz
      | linear_combination (-z ^ 13) * hz)

/-- `ζᵏ + ζ⁻ᵏ = 2 cos (2πk/16)`. -/
lemma zeta16_key (k : ℕ) :
    zeta16 ^ k + (zeta16 ^ k) ^ 15 = ((2 * Real.cos (2 * Real.pi * k / 16) : ℝ) : ℂ) := by
  have h1 : zeta16 ^ k = Complex.exp ((2 * Real.pi * k / 16 : ℝ) * Complex.I) := by
    rw [zeta16, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hne : zeta16 ^ k ≠ 0 := by
    rw [h1]; exact Complex.exp_ne_zero _
  have h15 : (zeta16 ^ k) ^ 15 = (zeta16 ^ k)⁻¹ := by
    field_simp
    exact zeta16_pow_k_pow16 k
  rw [h15, h1, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

lemma V16_apply (i k : Fin 16) : V16 i k = (zeta16 ^ (k : ℕ)) ^ (i : ℕ) := by
  simp [V16, Matrix.vandermonde_apply, ← pow_mul, mul_comm]

lemma V16_det_ne_zero : V16.det ≠ 0 := by
  rw [V16, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext (zeta16_prim.pow_inj a.isLt b.isLt hab)

/-- Diagonalisation identity: `A · V = V · diag(λ)`. -/
lemma C16adj_mul_V16 : C16adj * V16 = V16 * Matrix.diagonal lam16 := by
  ext i k
  have h := congrFun (C16adj_mulVec_geom (zeta16 ^ (k : ℕ)) (zeta16_pow_k_pow16 k)) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simp only [V16_apply]
  rw [h, zeta16_key]
  simp [lam16, mul_comm]

/-- **Hückel theory for the C₁₆ annulene.**  A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph `C₁₆` if and only if `μ = 2 cos (2πk/16)`
for some `k ∈ {0, 1, …, 15}`. -/
theorem huckel_C16 (μ : ℂ) :
    (∃ v : Fin 16 → ℂ, v ≠ 0 ∧ C16adj *ᵥ v = μ • v) ↔
      ∃ k : Fin 16, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 16) : ℝ) : ℂ) := by
  have hdet : IsUnit V16.det := isUnit_iff_ne_zero.mpr V16_det_ne_zero
  constructor
  · rintro ⟨w, hw0, hw⟩
    set u := V16⁻¹ *ᵥ w with hu
    have hVu : V16 *ᵥ u = w := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have h1 : V16 *ᵥ (Matrix.diagonal lam16 *ᵥ u) = V16 *ᵥ (μ • u) := by
      rw [Matrix.mulVec_mulVec, ← C16adj_mul_V16, ← Matrix.mulVec_mulVec, hVu, hw,
        Matrix.mulVec_smul, hVu]
    have h2 : Matrix.diagonal lam16 *ᵥ u = μ • u := by
      have h3 := congrArg (fun x => V16⁻¹ *ᵥ x) h1
      simpa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mul, Matrix.one_mulVec] using h3
    have hu0 : u ≠ 0 := by
      intro h
      exact hw0 (by rw [← hVu, h, Matrix.mulVec_zero])
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hu0
    refine ⟨k, ?_⟩
    have h4 := congrFun h2 k
    rw [Matrix.mulVec_diagonal] at h4
    simp only [Pi.smul_apply, smul_eq_mul] at h4
    have hk' : u k ≠ 0 := by simpa using hk
    have : lam16 k = μ := mul_right_cancel₀ hk' h4
    rw [← this, lam16]
  · rintro ⟨k, rfl⟩
    refine ⟨fun i => (zeta16 ^ (k : ℕ)) ^ (i : ℕ), ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · rw [C16adj_mulVec_geom _ (zeta16_pow_k_pow16 (k : ℕ)), zeta16_key]

end Chem

