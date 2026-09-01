/- Lean 4 requires `import` commands to precede any module doc comment;
   the required header comment follows immediately after the import. -/
import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
lemma normSq_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (h₁ : Wᴴ * W = 1) (h₂ : W * Wᴴ = 1) :
    (Matrix.of fun i j => ‖W i j‖ ^ 2) ∈ doublyStochastic ℝ (Fin d) := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by simp, fun i => ?_, fun j => ?_⟩
  · have h : ((∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have hii : (W * Wᴴ) i i = 1 := by rw [h₂]; simp
      rw [← hii, Matrix.mul_apply, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hz, Matrix.conjTranspose_apply]; rfl
    exact_mod_cast h
  · have h : ((∑ i, ‖W i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have hjj : (Wᴴ * W) j j = 1 := by rw [h₁]; simp
      rw [← hjj, Matrix.mul_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz, Matrix.conjTranspose_apply, Complex.star_def, mul_comm]
    exact_mod_cast h

/-- Trace of the product of two unitarily diagonalised matrices, expressed as a bilinear form in
the two diagonals against the entrywise squared moduli of the unitary `Uᴴ * V`. -/
lemma trace_mul_eq_sum (U V : Matrix (Fin d) (Fin d) ℂ) (mu nu : Fin d → ℝ) :
    Matrix.trace ((U * Matrix.diagonal (fun i => (mu i : ℂ)) * Uᴴ) *
        (V * Matrix.diagonal (fun i => (nu i : ℂ)) * Vᴴ)) =
      ((∑ i, ∑ j, mu i * nu j * ‖(Uᴴ * V) i j‖ ^ 2 : ℝ) : ℂ) := by
  set W := Uᴴ * V with hW
  have hWH : Wᴴ = Vᴴ * U := by rw [hW, conjTranspose_mul, conjTranspose_conjTranspose]
  have e1 : (U * Matrix.diagonal (fun i => (mu i : ℂ)) * Uᴴ) *
      (V * Matrix.diagonal (fun i => (nu i : ℂ)) * Vᴴ)
      = U * (Matrix.diagonal (fun i => (mu i : ℂ)) * W * Matrix.diagonal (fun i => (nu i : ℂ))
        * Vᴴ) := by rw [hW]; noncomm_ring
  rw [e1, trace_mul_comm]
  have e2 : (Matrix.diagonal (fun i => (mu i : ℂ)) * W * Matrix.diagonal (fun i => (nu i : ℂ))
        * Vᴴ) * U
      = Matrix.diagonal (fun i => (mu i : ℂ)) * W * Matrix.diagonal (fun i => (nu i : ℂ))
        * Wᴴ := by rw [hWH]; noncomm_ring
  rw [e2, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Complex.star_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ((‖W i j‖ : ℂ)) ^ 2 = W i j * (starRingEnd ℂ) (W i j) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [h]
  ring

/-- Key intermediate lemma (Birkhoff's theorem plus the rearrangement inequality): for a doubly
stochastic matrix `S` and antitone sequences `mu`, `nu`, the bilinear form
`∑ i j, mu i * nu j * S i j` is at most `∑ i, mu i * nu i`. -/
lemma sum_bilinear_doublyStochastic_le {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin d)) {mu nu : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, mu i * nu j * S i j ≤ ∑ i, mu i * nu i := by
  have hmono : Monovary mu nu := by
    intro i j h
    have hij : ¬ (i ≤ j) := fun hij => absurd (hnu hij) (not_le.2 h)
    exact hmu (le_of_lt (not_le.1 hij))
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have key : ∀ σ : Equiv.Perm (Fin d),
      ∑ i, ∑ j, mu i * nu j * (σ.permMatrix ℝ) i j ≤ ∑ i, mu i * nu i := by
    intro σ
    have h1 : ∀ i : Fin d, ∑ j, mu i * nu j * (σ.permMatrix ℝ) i j = mu i * nu (σ i) := by
      intro i
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    simpa [smul_eq_mul] using hmono.sum_smul_comp_perm_le_sum_smul (σ := σ)
  have hentry : ∀ i j, S i j = ∑ σ : Equiv.Perm (Fin d), w σ * (σ.permMatrix ℝ) i j := by
    intro i j
    conv_lhs => rw [← hwS]
    simp [Matrix.sum_apply]
  have hsplit : ∑ i, ∑ j, mu i * nu j * S i j
      = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, ∑ j, mu i * nu j * (σ.permMatrix ℝ) i j := by
    simp_rw [hentry, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => by ring
  rw [hsplit]
  calc ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, ∑ j, mu i * nu j * (σ.permMatrix ℝ) i j
      ≤ ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (key σ) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- A Hermitian matrix can be diagonalised by a unitary with its eigenvalues listed in any
prescribed order. -/
lemma exists_unitary_diagonalization {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    {mu : Fin d → ℝ} (e : Equiv.Perm (Fin d)) (hmu : mu = hA.eigenvalues ∘ e) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * Matrix.diagonal (fun i => (mu i : ℂ)) * Uᴴ := by
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at hspec
  set E : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hE
  have hE1 : Eᴴ * E = 1 := Unitary.coe_star_mul_self _
  have hE2 : E * Eᴴ = 1 := Unitary.coe_mul_star_self _
  refine ⟨E.submatrix id e, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      hE1, Matrix.submatrix_one_equiv]
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hE2,
      Matrix.submatrix_id_id]
  · have hd : Matrix.diagonal (fun i => (mu i : ℂ))
        = (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues : Fin d → ℂ)).submatrix e e := by
      rw [Matrix.submatrix_diagonal_equiv, hmu]
      rfl
    rw [hd, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    exact hspec

/-- **Von Neumann's trace inequality** for Hermitian matrices: if `mu` and `nu` list the
eigenvalues of the Hermitian matrices `A` and `B` in decreasing order (i.e. each is antitone and
is a rearrangement of the corresponding eigenvalue list), then
`Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
theorem vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (mu nu : Fin d → ℝ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hmuA : ∃ e : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ e)
    (hnuB : ∃ f : Equiv.Perm (Fin d), nu = hB.eigenvalues ∘ f) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨e, he⟩ := hmuA
  obtain ⟨f, hf⟩ := hnuB
  obtain ⟨U, hU₁, hU₂, hAU⟩ := exists_unitary_diagonalization hA e he
  obtain ⟨V, hV₁, hV₂, hBV⟩ := exists_unitary_diagonalization hB f hf
  rw [hAU, hBV, trace_mul_eq_sum U V mu nu, Complex.ofReal_re]
  refine sum_bilinear_doublyStochastic_le (S := Matrix.of fun i j => ‖(Uᴴ * V) i j‖ ^ 2)
    (normSq_mem_doublyStochastic ?_ ?_) hmu hnu
  · rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V := by noncomm_ring
      _ = 1 := by rw [hU₂]; simp [hV₁]
  · rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc Uᴴ * V * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * U := by noncomm_ring
      _ = 1 := by rw [hV₂]; simp [hU₁]

end Zeta23Redux.LinAlg

