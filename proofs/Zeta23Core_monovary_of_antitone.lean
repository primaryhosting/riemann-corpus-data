/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

namespace Zeta23Core

open Matrix

/-- Two antitone functions on a linear order monovary. -/
theorem monovary_of_antitone {ι : Type*} [LinearOrder ι] {a b : ι → ℝ}
    (ha : Antitone a) (hb : Antitone b) : Monovary a b := by
  intro i j hij
  rcases le_total j i with h | h
  · exact ha h
  · exact absurd (hb h) (not_le.2 hij)

/-- Averaging a product of monovarying weights against a doubly stochastic matrix is at most the
aligned sum `∑ i, a i * b i`.  This is the "doubly stochastic" form of the rearrangement
inequality, obtained from Birkhoff's theorem. -/
theorem sum_mul_le_of_mem_doublyStochastic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℝ} (hab : Monovary a b) {S : Matrix ι ι ℝ} (hS : S ∈ doublyStochastic ℝ ι) :
    ∑ j, ∑ k, S j k * (a j * b k) ≤ ∑ i, a i * b i := by
  obtain ⟨w, hw0, hw1, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  subst hw
  have key : ∀ σ : Equiv.Perm ι,
      ∑ j, ∑ k, (σ.permMatrix ℝ) j k * (a j * b k) ≤ ∑ i, a i * b i := by
    intro σ
    have h : ∀ j : ι, ∑ k, (σ.permMatrix ℝ) j k * (a j * b k) = a j * b (σ j) := by
      intro j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    rw [Finset.sum_congr rfl fun j _ => h j]
    simpa [smul_eq_mul] using hab.sum_smul_comp_perm_le_sum_smul (σ := σ)
  have hsplit : ∀ j : ι, ∑ k : ι, ∑ σ : Equiv.Perm ι, w σ * ((σ.permMatrix ℝ) j k * (a j * b k))
      = ∑ σ : Equiv.Perm ι, ∑ k : ι, w σ * ((σ.permMatrix ℝ) j k * (a j * b k)) :=
    fun _ => Finset.sum_comm
  calc ∑ j, ∑ k, (∑ σ, w σ • σ.permMatrix ℝ) j k * (a j * b k)
      = ∑ σ : Equiv.Perm ι, w σ * ∑ j, ∑ k, (σ.permMatrix ℝ) j k * (a j * b k) := by
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
          Finset.sum_mul, mul_assoc]
        rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_comm]
    _ ≤ ∑ _σ : Equiv.Perm ι, w _σ * ∑ i, a i * b i :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (key σ) (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/
theorem weights_mem_doublyStochastic {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {W : Matrix ι ι 𝕜} (h1 : W * Wᴴ = 1) (h2 : Wᴴ * W = 1) :
    (Matrix.of fun j k => ‖W j k‖ ^ 2) ∈ doublyStochastic ℝ ι := by
  rw [mem_doublyStochastic_iff_sum]
  simp only [Matrix.of_apply]
  refine ⟨fun i j => by positivity, fun i => ?_, fun j => ?_⟩
  · have h := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, RCLike.star_def, Matrix.one_apply_eq] at h
    have h3 : ∀ k, W i k * (starRingEnd 𝕜) (W i k) = ((‖W i k‖ ^ 2 : ℝ) : 𝕜) := by
      intro k
      rw [RCLike.mul_conj]
      norm_cast
    rw [Finset.sum_congr rfl fun k _ => h3 k, ← RCLike.ofReal_sum] at h
    exact_mod_cast h
  · have h := congrFun (congrFun h2 j) j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, RCLike.star_def, Matrix.one_apply_eq] at h
    have h3 : ∀ k, (starRingEnd 𝕜) (W k j) * W k j = ((‖W k j‖ ^ 2 : ℝ) : 𝕜) := by
      intro k
      rw [RCLike.conj_mul]
      norm_cast
    rw [Finset.sum_congr rfl fun k _ => h3 k, ← RCLike.ofReal_sum] at h
    exact_mod_cast h

/-- The trace of `diagonal α * W * diagonal β * Wᴴ` in terms of the squared absolute values of the
entries of `W`. -/
theorem trace_diagonal_mul_mul_diagonal_mul_conjTranspose {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n] [DecidableEq n] (W : Matrix n n 𝕜) (α β : n → ℝ) :
    (diagonal (RCLike.ofReal ∘ α) * W * diagonal (RCLike.ofReal ∘ β) * Wᴴ).trace
      = ((∑ j, ∑ k, ‖W j k‖ ^ 2 * (α j * β k) : ℝ) : 𝕜) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.conjTranspose_apply, RCLike.star_def]
  have h : W j k * (starRingEnd 𝕜) (W j k) = ((‖W j k‖ : 𝕜)) ^ 2 := RCLike.mul_conj _
  linear_combination ((α j : 𝕜) * (β k : 𝕜)) * h

/-- `Re tr(A * B)` is an average of products of eigenvalues of `A` and `B` against a doubly
stochastic weight matrix. -/
theorem exists_doublyStochastic_trace_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ S ∈ doublyStochastic ℝ n,
      RCLike.re (A * B).trace
        = ∑ j, ∑ k, S j k * (hA.eigenvalues j * hB.eigenvalues k) := by
  have hA' : A = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, mul_assoc]
  have hB' : B = (hB.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (RCLike.ofReal ∘ hB.eigenvalues) * star (hB.eigenvectorUnitary : Matrix n n 𝕜) := by
    conv_lhs => rw [hB.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, mul_assoc]
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hV
  set Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDa
  set Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hB.eigenvalues) with hDb
  have hUs : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUs' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hVs : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVs' : V * star V = 1 := Unitary.coe_mul_star_self _
  set W : Matrix n n 𝕜 := star U * V with hW
  have hWs : star W = star V * U := by rw [hW, Matrix.star_mul, star_star]
  have hW1 : W * Wᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hWs, hW, mul_assoc, ← mul_assoc V (star V) U, hVs',
      one_mul, hUs]
  have hW2 : Wᴴ * W = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hWs, hW, mul_assoc, ← mul_assoc U (star U) V, hUs',
      one_mul, hVs]
  have hAB : A * B = U * (Da * W * Db * Wᴴ) * star U := by
    rw [hA', hB', hW, ← Matrix.star_eq_conjTranspose, hWs]
    simp only [mul_assoc]
    rw [hUs', mul_one]
  have htr : (A * B).trace = (Da * W * Db * Wᴴ).trace := by
    rw [hAB, Matrix.trace_mul_comm, ← mul_assoc, hUs, one_mul]
  refine ⟨Matrix.of fun j k => ‖W j k‖ ^ 2, weights_mem_doublyStochastic hW1 hW2, ?_⟩
  rw [htr, hDa, hDb, trace_diagonal_mul_mul_diagonal_mul_conjTranspose W hA.eigenvalues
    hB.eigenvalues]
  simp

/-- **Von Neumann trace inequality, Hermitian case.**
For Hermitian matrices `A`, `B` over an `RCLike` field indexed by a finite type, `Re tr(A * B)`
is at most `∑ i, a i * b i`, where `a` and `b` are the eigenvalues of `A` and `B` sorted in
decreasing order (`Matrix.IsHermitian.eigenvalues₀` is the antitone enumeration of the
eigenvalues, indexed by `Fin (Fintype.card n)`). -/
theorem vonNeumann_trace_ineq_hermitian {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  obtain ⟨S, hS, hSeq⟩ := exists_doublyStochastic_trace_eq hA hB
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  have hval : ∀ i : n, hA.eigenvalues i = hA.eigenvalues₀ (e.symm i) := fun _ => rfl
  have hvalB : ∀ i : n, hB.eigenvalues i = hB.eigenvalues₀ (e.symm i) := fun _ => rfl
  have hS' : S.reindex e.symm e.symm ∈ doublyStochastic ℝ (Fin (Fintype.card n)) :=
    reindex_mem_doublyStochastic hS
  have hmono : Monovary hA.eigenvalues₀ hB.eigenvalues₀ :=
    monovary_of_antitone hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone
  have hsum : ∑ j, ∑ k, S j k * (hA.eigenvalues j * hB.eigenvalues k)
      = ∑ j, ∑ k, (S.reindex e.symm e.symm) j k
          * (hA.eigenvalues₀ j * hB.eigenvalues₀ k) := by
    rw [← Equiv.sum_comp e (fun j => ∑ k, S j k * (hA.eigenvalues j * hB.eigenvalues k))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Equiv.sum_comp e (fun k => S (e j) k * (hA.eigenvalues (e j) * hB.eigenvalues k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hval, hvalB, Matrix.reindex_apply]
  rw [hSeq, hsum]
  exact sum_mul_le_of_mem_doublyStochastic hmono hS'

end Zeta23Core

