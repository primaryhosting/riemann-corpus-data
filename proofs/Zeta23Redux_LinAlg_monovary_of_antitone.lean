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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Von Neumann's trace inequality for Hermitian complex matrices: if `A = U * diagonal mu * Uᴴ`
and `B = V * diagonal nu * Vᴴ` with `U`, `V` unitary and the real eigenvalue tuples `mu`, `nu`
both listed in decreasing (antitone) order, then
`(trace (A * B)).re ≤ ∑ i, mu i * nu i`.

The route is the classical one: diagonalise, so that the trace becomes a bilinear form of `mu`
and `nu` against the entrywise squared modulus of the unitary `W = Uᴴ * V`, which is doubly
stochastic; then apply Birkhoff's theorem (`exists_eq_sum_perm_of_mem_doublyStochastic`) and the
rearrangement inequality (`Monovary.sum_smul_comp_perm_le_sum_smul`).
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- Two antitone real tuples monovary. -/
lemma monovary_of_antitone {mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu) :
    Monovary mu nu := by
  intro i j hij
  rcases le_total j i with h | h
  · exact hmu h
  · exact absurd (hnu h) (not_le.2 hij)

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
lemma normSq_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ (Fin d) := by
  have h1 : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hW
  have h2 : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.1 hW
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have := congrFun (congrFun h1 i) i
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj] at this
    simp only [Matrix.of_apply]
    exact_mod_cast this
  · have := congrFun (congrFun h2 j) j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.conj_mul'] at this
    simp only [Matrix.of_apply, Complex.normSq_eq_norm_sq]
    exact_mod_cast this

/-- The bilinear form of two monovarying tuples against a doubly stochastic matrix is at most the
aligned sum.  This is the Birkhoff + rearrangement step of von Neumann's trace inequality. -/
lemma sum_bilin_le_of_doublyStochastic {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin d)) {mu nu : Fin d → ℝ} (hmv : Monovary mu nu) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hw3⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have expand : ∀ i j, S i j = ∑ σ : Equiv.Perm (Fin d), w σ * (σ.permMatrix ℝ) i j := by
    intro i j
    rw [← hw3]
    simp [Matrix.sum_apply]
  have key : ∀ σ : Equiv.Perm (Fin d),
      ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (mu i * nu j) = ∑ i, mu i * nu (σ i) := by
    intro σ
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hEq : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) := by
    calc ∑ i, ∑ j, S i j * (mu i * nu j)
        = ∑ i, ∑ σ : Equiv.Perm (Fin d), ∑ j, w σ * ((σ.permMatrix ℝ) i j * (mu i * nu j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [expand i j, Finset.sum_mul]
          exact Finset.sum_congr rfl fun σ _ => by ring
      _ = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [← key σ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [hEq]
  have hstep : ∀ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) ≤ w σ * ∑ i, mu i * nu i :=
    fun σ => mul_le_mul_of_nonneg_left
      (by simpa using hmv.sum_smul_comp_perm_le_sum_smul (σ := σ)) (hw0 σ)
  calc ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i)
      ≤ ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ => hstep σ
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Diagonal entry of the conjugated product: `(Dμ * W * Dν * Wᴴ) i i = ∑ j, mu i * nu j * |W i j|²`. -/
lemma diag_entry_conj (W : Matrix (Fin d) (Fin d) ℂ) (mu nu : Fin d → ℝ) (i : Fin d) :
    (Matrix.diagonal (fun i => (mu i : ℂ)) * W * Matrix.diagonal (fun i => (nu i : ℂ)) * Wᴴ) i i
      = ((∑ j, mu i * nu j * Complex.normSq (W i j) : ℝ) : ℂ) := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((mu i : ℂ)) * W i j * (nu j : ℂ) * (starRingEnd ℂ) (W i j)
      = (mu i : ℂ) * (nu j : ℂ) * (W i j * (starRingEnd ℂ) (W i j)) by ring, Complex.mul_conj]

/-- Cyclicity of the trace turns `trace (A * B)` into a trace conjugated by `W = Uᴴ * V`. -/
lemma trace_eq_conj_trace {A B : Matrix (Fin d) (Fin d) ℂ} {mu nu : Fin d → ℝ}
    {U V : Matrix (Fin d) (Fin d) ℂ}
    (hA : A = U * Matrix.diagonal (fun i => (mu i : ℂ)) * Uᴴ)
    (hB : B = V * Matrix.diagonal (fun i => (nu i : ℂ)) * Vᴴ) :
    Matrix.trace (A * B)
      = Matrix.trace (Matrix.diagonal (fun i => (mu i : ℂ)) * (Uᴴ * V)
          * Matrix.diagonal (fun i => (nu i : ℂ)) * (Uᴴ * V)ᴴ) := by
  subst hA hB
  have hWH : (Uᴴ * V)ᴴ = Vᴴ * U := by simp [Matrix.conjTranspose_mul]
  rw [hWH]
  calc Matrix.trace (U * Matrix.diagonal (fun i => (mu i : ℂ)) * Uᴴ *
        (V * Matrix.diagonal (fun i => (nu i : ℂ)) * Vᴴ))
      = Matrix.trace (U * (Matrix.diagonal (fun i => (mu i : ℂ)) * Uᴴ * V *
          Matrix.diagonal (fun i => (nu i : ℂ)) * Vᴴ)) := by congr 1; noncomm_ring
    _ = Matrix.trace ((Matrix.diagonal (fun i => (mu i : ℂ)) * Uᴴ * V *
          Matrix.diagonal (fun i => (nu i : ℂ)) * Vᴴ) * U) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; noncomm_ring

/--
**Von Neumann's trace inequality** for Hermitian complex matrices.

If `A` and `B` are Hermitian matrices of size `Fin d`, given through their spectral
decompositions `A = U * diagonal mu * Uᴴ`, `B = V * diagonal nu * Vᴴ` with `U`, `V` unitary
and the real eigenvalue tuples `mu` and `nu` both listed in the same (decreasing) monotone order,
then `Re (trace (A * B)) ≤ ∑ i, mu i * nu i`.

Note that the hypotheses force `A` and `B` to be Hermitian, since `mu` and `nu` are real-valued.
-/
theorem vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ} {mu nu : Fin d → ℝ}
    {U V : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hA : A = U * Matrix.diagonal (fun i => (mu i : ℂ)) * Uᴴ)
    (hB : B = V * Matrix.diagonal (fun i => (nu i : ℂ)) * Vᴴ)
    (hmu : Antitone mu) (hnu : Antitone nu) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  have hW : (Uᴴ * V) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have h1 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hV
    have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    have hs : star (Uᴴ * V) = Vᴴ * U := by
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
    rw [hs]
    calc Uᴴ * V * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * U := by noncomm_ring
      _ = 1 := by rw [h1, mul_one, h2]
  have htr : Matrix.trace (A * B)
      = ((∑ i, ∑ j, mu i * nu j * Complex.normSq ((Uᴴ * V) i j) : ℝ) : ℂ) := by
    rw [trace_eq_conj_trace hA hB, Matrix.trace, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => diag_entry_conj (Uᴴ * V) mu nu i
  rw [htr, Complex.ofReal_re]
  have hS := normSq_mem_doublyStochastic hW
  have := sum_bilin_le_of_doublyStochastic hS (monovary_of_antitone hmu hnu)
  refine le_trans (le_of_eq ?_) this
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [Matrix.of_apply]; ring

/-! ## Reformulation in terms of Mathlib's eigenvalues of a Hermitian matrix -/

/-- Permuting the columns of a unitary matrix keeps it unitary. -/
lemma unitaryGroup_submatrix_perm {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (e : Equiv.Perm (Fin d)) :
    (U.submatrix id e) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  ext a b
  have := congrFun (congrFun h1 a) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq,
    Matrix.star_eq_conjTranspose] at *
  rw [← this]
  exact Equiv.sum_comp e (fun j => U a j * (starRingEnd ℂ) (U b j))

/-- Permuting the eigenvalues and the corresponding eigenvectors simultaneously does not change
the diagonalised matrix. -/
lemma conj_diagonal_perm (U : Matrix (Fin d) (Fin d) ℂ) (e : Equiv.Perm (Fin d)) (g : Fin d → ℝ) :
    (U.submatrix id e) * Matrix.diagonal (fun i => ((g (e i) : ℝ) : ℂ)) * (U.submatrix id e)ᴴ
      = U * Matrix.diagonal (fun i => (g i : ℂ)) * Uᴴ := by
  ext a b
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun j => U a j * (g j : ℂ) * (starRingEnd ℂ) (U b j))

/-- Unitary diagonalisation of a Hermitian matrix, in the explicit `U * diagonal λ * Uᴴ` form. -/
lemma isHermitian_eq_conj_diagonal_eigenvalues {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
        * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
        * (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]

/-- Any real tuple can be reindexed by a permutation so as to become antitone (decreasing).
This shows the hypotheses of `vonNeumann_trace_ineq_eigenvalues` can always be met. -/
lemma exists_antitone_perm (g : Fin d → ℝ) : ∃ e : Equiv.Perm (Fin d), Antitone (g ∘ e) := by
  refine ⟨(Fin.revPerm).trans (Tuple.sort g), fun i j hij => ?_⟩
  exact Tuple.monotone_sort g (Fin.rev_le_rev.2 hij)

/--
**Von Neumann's trace inequality**, stated with Mathlib's eigenvalues of Hermitian matrices.

If `A`, `B` are Hermitian and `mu`, `nu` are the eigenvalue tuples of `A` and `B` (reindexed by
permutations `e`, `f`), both listed in decreasing order, then
`Re (trace (A * B)) ≤ ∑ i, mu i * nu i`.
-/
theorem vonNeumann_trace_ineq_eigenvalues {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {mu nu : Fin d → ℝ} {e f : Equiv.Perm (Fin d)}
    (hmu : mu = hA.eigenvalues ∘ e) (hnu : nu = hB.eigenvalues ∘ f)
    (hmuA : Antitone mu) (hnuA : Antitone nu) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  subst hmu hnu
  refine vonNeumann_trace_ineq
    (U := ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)).submatrix id e)
    (V := ((hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)).submatrix id f)
    (unitaryGroup_submatrix_perm hA.eigenvectorUnitary.2 e)
    (unitaryGroup_submatrix_perm hB.eigenvectorUnitary.2 f) ?_ ?_ hmuA hnuA
  · simp only [Function.comp_apply]
    rw [conj_diagonal_perm]
    exact isHermitian_eq_conj_diagonal_eigenvalues hA
  · simp only [Function.comp_apply]
    rw [conj_diagonal_perm]
    exact isHermitian_eq_conj_diagonal_eigenvalues hB

end Zeta23Redux.LinAlg

