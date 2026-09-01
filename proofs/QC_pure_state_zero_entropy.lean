/-
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- repeated verbatim as a module docstring immediately after the import.)

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open Matrix

set_option maxHeartbeats 1000000

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed via its
(real) eigenvalues: `S(ρ) = -∑ λᵢ log λᵢ`.  (Recall `Real.log 0 = 0`, so the usual convention
`0 log 0 = 0` is automatic.) -/
noncomputable def vonNeumannEntropy (ρ : Matrix n n ℂ) (hρ : ρ.IsHermitian) : ℝ :=
  -∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i)

/-- A density matrix is a *pure state* if it is of the form `|ψ⟩⟨ψ|` for a unit vector `ψ`. -/
def IsPureState (ρ : Matrix n n ℂ) : Prop :=
  ∃ ψ : n → ℂ, (∑ i, ‖ψ i‖ ^ 2 = 1) ∧ ρ = Matrix.vecMulVec ψ (star ψ)

omit [DecidableEq n] in
/-- A pure state `|ψ⟩⟨ψ|` is Hermitian. -/
theorem IsPureState.isHermitian {ρ : Matrix n n ℂ} (h : IsPureState ρ) : ρ.IsHermitian := by
  obtain ⟨ψ, -, rfl⟩ := h
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

omit [DecidableEq n] in
/-- A pure state has unit trace. -/
theorem IsPureState.trace_eq_one {ρ : Matrix n n ℂ} (h : IsPureState ρ) : ρ.trace = 1 := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  have : ∀ i : n, ψ i * (star ψ) i = (‖ψ i‖ ^ 2 : ℝ) := by
    intro i
    rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, this]
  rw [← Complex.ofReal_sum, hψ, Complex.ofReal_one]

omit [DecidableEq n] in
/-- A pure state is an idempotent matrix (an orthogonal projection of rank one). -/
theorem IsPureState.mul_self {ρ : Matrix n n ℂ} (h : IsPureState ρ) : ρ * ρ = ρ := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  have hsum : ∑ k : n, (star ψ) k * ψ k = 1 := by
    have : ∀ k : n, (star ψ) k * ψ k = (‖ψ k‖ ^ 2 : ℝ) := by
      intro k
      rw [Pi.star_apply, RCLike.star_def, mul_comm, Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq _
    simp only [this]
    rw [← Complex.ofReal_sum, hψ, Complex.ofReal_one]
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  calc ∑ k : n, ψ i * (star ψ) k * (ψ k * (star ψ) j)
      = (ψ i * (star ψ) j) * ∑ k : n, (star ψ) k * ψ k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ = ψ i * (star ψ) j := by rw [hsum, mul_one]

/-- Every eigenvalue of a Hermitian idempotent matrix is `0` or `1`. -/
theorem eigenvalue_eq_zero_or_one {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hidem : ρ * ρ = ρ)
    (i : n) : hρ.eigenvalues i = 0 ∨ hρ.eigenvalues i = 1 := by
  set lam : ℝ := hρ.eigenvalues i with hlam
  set v : n → ℂ := ⇑(hρ.eigenvectorBasis i) with hv
  have hmul : ρ *ᵥ v = lam • v := hρ.mulVec_eigenvectorBasis i
  have h1 : (ρ * ρ) *ᵥ v = (lam * lam) • v := by
    rw [← Matrix.mulVec_mulVec, hmul, Matrix.mulVec_smul, hmul, smul_smul]
  rw [hidem, hmul] at h1
  -- `v` is nonzero, so `lam * lam = lam`
  have hvne : v ≠ 0 := by
    intro h0
    have : ‖hρ.eigenvectorBasis i‖ = 1 := hρ.eigenvectorBasis.orthonormal.1 i
    rw [show (hρ.eigenvectorBasis i) = 0 from by
      ext k; simpa using congrFun h0 k] at this
    simp at this
  obtain ⟨k, hk⟩ : ∃ k : n, v k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hvne (funext hc)
  have hcoord := congrFun h1 k
  simp only [Pi.smul_apply, Complex.real_smul] at hcoord
  have h2 : (lam : ℂ) = ((lam * lam : ℝ) : ℂ) := mul_right_cancel₀ hk hcoord
  have hreal : lam = lam * lam := by exact_mod_cast h2
  rcases mul_eq_zero.mp (show lam * (lam - 1) = 0 by nlinarith) with h | h
  · exact Or.inl h
  · right; linarith

/-- **The von Neumann entropy of a pure state is zero.** -/
theorem pure_state_zero_entropy {ρ : Matrix n n ℂ} (hpure : IsPureState ρ) :
    vonNeumannEntropy ρ hpure.isHermitian = 0 := by
  unfold vonNeumannEntropy
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro i _
  rcases eigenvalue_eq_zero_or_one hpure.isHermitian hpure.mul_self i with h | h <;>
    simp [h]

end QC

#print axioms QC.pure_state_zero_entropy

