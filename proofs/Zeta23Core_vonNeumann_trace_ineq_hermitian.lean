import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a unitary matrix `W`, the matrix of squared norms of the entries of `W` is doubly
stochastic: its rows sum to `1` because `W * Wᴴ = 1`, and its columns sum to `1` because
`Wᴴ * W = 1`. -/
lemma unitary_normSq_mem_doublyStochastic {W : Matrix n n 𝕜} (hW : W ∈ Matrix.unitaryGroup n 𝕜) :
    (Matrix.of fun j k => ‖W j k‖ ^ 2) ∈ doublyStochastic ℝ n := by
  have h1 : W * star W = 1 := hW.2
  have h2 : star W * W = 1 := hW.1
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h := congrFun (congrFun h1 i) i
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply, RCLike.star_def] at h
    have : ((∑ x, ‖W i x‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      simpa [RCLike.mul_conj] using h
    exact_mod_cast this
  · have h := congrFun (congrFun h2 j) j
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply, RCLike.star_def] at h
    have : ((∑ x, ‖W x j‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      simpa [RCLike.conj_mul] using h
    exact_mod_cast this

/-- Birkhoff–von Neumann plus rearrangement: if `a` and `b` are antitone and `M` is doubly
stochastic, then `∑ j k, a j * b k * M j k ≤ ∑ i, a i * b i`. -/
lemma sum_mul_doublyStochastic_le {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {a b : ι → ℝ} (ha : Antitone a) (hb : Antitone b) {M : Matrix ι ι ℝ}
    (hM : M ∈ doublyStochastic ℝ ι) :
    ∑ j, ∑ k, a j * b k * M j k ≤ ∑ i, a i * b i := by
  obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hmono : Monovary a b := ha.monovary hb
  have expand : ∀ j k, M j k = ∑ σ : Equiv.Perm ι, w σ * (σ.permMatrix ℝ) j k := by
    intro j k
    rw [← hwM]
    simp [Matrix.sum_apply]
  have key : ∀ σ : Equiv.Perm ι, ∑ j, ∑ k, a j * b k * (σ.permMatrix ℝ) j k
      = ∑ j, a j * b (σ j) := by
    intro σ
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have step1 : ∀ j : ι, ∑ k, a j * b k * M j k
      = ∑ σ : Equiv.Perm ι, ∑ k, w σ * (a j * b k * (σ.permMatrix ℝ) j k) := by
    intro j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [expand j k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  calc ∑ j, ∑ k, a j * b k * M j k
      = ∑ σ : Equiv.Perm ι, w σ * ∑ j, ∑ k, a j * b k * (σ.permMatrix ℝ) j k := by
        simp_rw [step1]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm ι, w σ * ∑ j, a j * b (σ j) :=
        Finset.sum_congr rfl fun σ _ => by rw [key σ]
    _ ≤ ∑ σ : Equiv.Perm ι, w σ * ∑ j, a j * b j :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hmono.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The real part of the trace of a product of two unitarily diagonalized Hermitian matrices,
written as `∑ j k, a j * b k * |W j k|²` for the unitary `W = Uᴴ V`. -/
lemma re_trace_conj_diag {U V : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) (a b : n → ℝ) :
    RCLike.re (Matrix.trace ((U * Matrix.diagonal (RCLike.ofReal ∘ a) * star U) *
        (V * Matrix.diagonal (RCLike.ofReal ∘ b) * star V)))
      = ∑ j, ∑ k, a j * b k * ‖(star U * V) j k‖ ^ 2 := by
  set W : Matrix n n 𝕜 := star U * V with hWdef
  set Da : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ a) with hDa
  set Db : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ b) with hDb
  have hUU : U * star U = 1 := hU.2
  have hUU' : star U * U = 1 := hU.1
  have hstarW : star W = star V * U := by rw [hWdef, Matrix.star_mul, star_star]
  have hprod : (U * Da * star U) * (V * Db * star V) = U * (Da * W * Db * star W) * star U := by
    rw [hstarW, hWdef]
    simp only [← mul_assoc]
    rw [mul_assoc _ U (star U), hUU, mul_one]
  rw [hprod, Matrix.trace_mul_cycle, ← mul_assoc, hUU', one_mul]
  have hentry : Matrix.trace (Da * W * Db * star W)
      = ((∑ j, ∑ k, a j * b k * ‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
    rw [Matrix.trace]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hDa, hDb]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, RCLike.star_def,
      Function.comp_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hc : W j k * (starRingEnd 𝕜) (W j k) = ((‖W j k‖ : 𝕜)) ^ 2 := RCLike.mul_conj _
    linear_combination ((a j : 𝕜) * (b k : 𝕜)) * hc
  rw [hentry]
  simp

/-- **Von Neumann trace inequality**, Hermitian case: for Hermitian matrices `A`, `B` over an
`RCLike` field indexed by a finite type, `Re (tr (A * B))` is at most the sum of the products of
the eigenvalues of `A` and of `B`, each listed in decreasing order.

Here the decreasing enumeration of the eigenvalues is `Matrix.IsHermitian.eigenvalues₀`, which is
antitone by `Matrix.IsHermitian.eigenvalues₀_antitone`. -/
theorem vonNeumann_trace_ineq_hermitian {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    RCLike.re (Matrix.trace (A * B)) ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hU : U ∈ Matrix.unitaryGroup n 𝕜 := hA.eigenvectorUnitary.2
  have hV : V ∈ Matrix.unitaryGroup n 𝕜 := hB.eigenvectorUnitary.2
  have hA' : A = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [hUdef]
  have hB' : B = V * Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) * star V := by
    conv_lhs => rw [hB.spectral_theorem]
    simp [hVdef]
  have hW : (star U * V) ∈ Matrix.unitaryGroup n 𝕜 := mul_mem (Unitary.star_mem hU) hV
  set M : Matrix n n ℝ := Matrix.of fun j k => ‖(star U * V) j k‖ ^ 2 with hM
  have hMds : M ∈ doublyStochastic ℝ n := unitary_normSq_mem_doublyStochastic hW
  have hMsub : M.submatrix e e ∈ doublyStochastic ℝ (Fin (Fintype.card n)) := by
    have := reindex_mem_doublyStochastic (e₁ := e.symm) (e₂ := e.symm) hMds
    simpa [Matrix.reindex] using this
  have heig : ∀ j, hA.eigenvalues (e j) = hA.eigenvalues₀ j := by
    intro j; simp [he, Matrix.IsHermitian.eigenvalues]
  have heig' : ∀ j, hB.eigenvalues (e j) = hB.eigenvalues₀ j := by
    intro j; simp [he, Matrix.IsHermitian.eigenvalues]
  calc RCLike.re (Matrix.trace (A * B))
      = ∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k * ‖(star U * V) j k‖ ^ 2 := by
        conv_lhs => rw [hA', hB']
        exact re_trace_conj_diag hU _ _
    _ = ∑ j, ∑ k, hA.eigenvalues₀ j * hB.eigenvalues₀ k * (M.submatrix e e) j k := by
        rw [← Equiv.sum_comp e (fun j => ∑ k, hA.eigenvalues j * hB.eigenvalues k *
          ‖(star U * V) j k‖ ^ 2)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Equiv.sum_comp e (fun k => hA.eigenvalues (e j) * hB.eigenvalues k *
          ‖(star U * V) (e j) k‖ ^ 2)]
        exact Finset.sum_congr rfl fun k _ => by simp [heig, heig', hM]
    _ ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i :=
        sum_mul_doublyStochastic_le hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone hMsub

end Zeta23Core

