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

/-- Birkhoff + rearrangement: for antitone `mu`, `nu` and a doubly stochastic matrix `S`,
the bilinear form `∑ i j, S i j * (mu i * nu j)` is at most `∑ i, mu i * nu i`. -/
lemma sum_bilinear_le_of_mem_doublyStochastic {d : ℕ} {mu nu : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin d)) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have key : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) := by
    rw [← hwS]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, smul_eq_mul, Option.mem_some_iff, Finset.sum_mul]
    calc ∑ x : Fin d, ∑ y : Fin d, ∑ σ : Equiv.Perm (Fin d),
            (w σ * if σ x = y then 1 else 0) * (mu x * nu y)
        = ∑ x : Fin d, ∑ σ : Equiv.Perm (Fin d), ∑ y : Fin d,
            (w σ * if σ x = y then 1 else 0) * (mu x * nu y) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ σ : Equiv.Perm (Fin d), ∑ x : Fin d, ∑ y : Fin d,
            (w σ * if σ x = y then 1 else 0) * (mu x * nu y) := Finset.sum_comm
      _ = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [Finset.sum_ite_eq]
  rw [key]
  have hmono : Monovary mu nu := hmu.monovary hnu
  calc ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i)
      ≤ ∑ _σ : Equiv.Perm (Fin d), w _σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hmono.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
lemma sq_abs_mem_doublyStochastic {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun i j => ‖W i j‖ ^ 2) ∈ doublyStochastic ℝ (Fin d) := by
  have hnorm : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ : ℝ) : ℂ) ^ 2 := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have h1 : W * Wᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff).1 hW
  have h2 : Wᴴ * W = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').1 hW
  rw [mem_doublyStochastic_iff_sum]
  simp only [Matrix.of_apply]
  refine ⟨fun i j => by positivity, fun i => ?_, fun j => ?_⟩
  · have h : ((∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      have hii := congrFun (congrFun h1 i) i
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hii
      rw [← hii]
      exact Finset.sum_congr rfl fun j _ => by rw [Complex.star_def, hnorm]
    exact_mod_cast h
  · have h : ((∑ i, ‖W i j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      have hjj := congrFun (congrFun h2 j) j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hjj
      rw [← hjj]
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.star_def, mul_comm, hnorm]
    exact_mod_cast h

/-- The trace of `diagonal mu * W * diagonal nu * Wᴴ` in terms of the squared moduli of `W`. -/
lemma trace_diagonal_mul_mul_diagonal_mul_conjTranspose {d : ℕ} (mu nu : Fin d → ℝ)
    (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (diagonal (fun i => (mu i : ℂ)) * W * diagonal (fun j => (nu j : ℂ)) * Wᴴ)
      = ((∑ i, ∑ j, ‖W i j‖ ^ 2 * (mu i * nu j) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    mul_ite, mul_zero, Finset.sum_ite_eq']
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : W i j * (starRingEnd ℂ) (W i j) = ((‖W i j‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [Complex.star_def]
  linear_combination ((mu i : ℂ) * (nu j : ℂ)) * h

/-- The eigenvalues of a Hermitian matrix can always be listed in decreasing order:
there is a permutation `e` of the index type with `hA.eigenvalues ∘ e` antitone.
(This shows that the hypotheses of `vonNeumann_trace_ineq` below are satisfiable.) -/
theorem exists_antitone_eigenvalues_perm {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) : ∃ e : Equiv.Perm (Fin d), Antitone (hA.eigenvalues ∘ e) := by
  classical
  set q : Fin (Fintype.card (Fin d)) ≃ Fin d := Fintype.equivOfCardEq (Fintype.card_fin _) with hq
  refine ⟨(finCongr (Fintype.card_fin d).symm).trans q, ?_⟩
  have hmono : Monotone (finCongr (Fintype.card_fin d).symm) := by
    intro a b hab; simpa using hab
  have hcomp : (hA.eigenvalues ∘ ((finCongr (Fintype.card_fin d).symm).trans q))
      = hA.eigenvalues₀ ∘ (finCongr (Fintype.card_fin d).symm) := by
    funext i
    simp [Matrix.IsHermitian.eigenvalues, hq]
  rw [hcomp]
  exact hA.eigenvalues₀_antitone.comp_monotone hmono

/-- **Von Neumann's trace inequality** for Hermitian matrices.
If `mu` and `nu` list the eigenvalues of the Hermitian matrices `A` and `B` respectively
(each in some order, given by permutations `eA`, `eB`), and both lists are in decreasing
(antitone) order, then `Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
theorem vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {mu nu : Fin d → ℝ}
    {eA eB : Equiv.Perm (Fin d)} (hmuA : mu = hA.eigenvalues ∘ eA)
    (hnuB : nu = hB.eigenvalues ∘ eB) (hmu : Antitone mu) (hnu : Antitone nu) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    with hUdef
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    with hVdef
  set Dmu : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) with hDmu
  set Dnu : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) with hDnu
  have hAeq : A = U * Dmu * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [hUdef, hDmu, Function.comp_def]
  have hBeq : B = V * Dnu * star V := by
    conv_lhs => rw [hB.spectral_theorem]
    simp [hVdef, hDnu, Function.comp_def]
  set W : Matrix (Fin d) (Fin d) ℂ := star U * V with hWdef
  have hWmem : W ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [hWdef, hUdef, hVdef]
    exact Submonoid.mul_mem _ (Unitary.star_mem hA.eigenvectorUnitary.2)
      hB.eigenvectorUnitary.2
  have hWstar : Wᴴ = star V * U := by
    rw [← Matrix.star_eq_conjTranspose, hWdef, Matrix.star_mul, star_star]
  -- rewrite the trace
  have htr : Matrix.trace (A * B) = Matrix.trace (Dmu * W * Dnu * Wᴴ) := by
    rw [hWstar, hWdef, hAeq, hBeq]
    rw [show U * Dmu * star U * (V * Dnu * star V)
        = U * (Dmu * star U * V * Dnu * star V) from by simp only [mul_assoc]]
    rw [Matrix.trace_mul_comm]
    congr 1
    simp only [mul_assoc]
  rw [htr, trace_diagonal_mul_mul_diagonal_mul_conjTranspose, Complex.ofReal_re]
  -- reindex the doubly stochastic matrix
  set S : Matrix (Fin d) (Fin d) ℝ :=
    (Matrix.of fun i j => ‖W i j‖ ^ 2).reindex eA.symm eB.symm with hSdef
  have hSmem : S ∈ doublyStochastic ℝ (Fin d) :=
    reindex_mem_doublyStochastic (sq_abs_mem_doublyStochastic hWmem)
  have hSapply : ∀ i j, S i j = ‖W (eA i) (eB j)‖ ^ 2 := by
    intro i j; simp [hSdef]
  have hreindex : ∑ i, ∑ j, ‖W i j‖ ^ 2 * (hA.eigenvalues i * hB.eigenvalues j)
      = ∑ i, ∑ j, S i j * (mu i * nu j) := by
    rw [← Equiv.sum_comp eA (fun i => ∑ j, ‖W i j‖ ^ 2 * (hA.eigenvalues i * hB.eigenvalues j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp eB
      (fun j => ‖W (eA i) j‖ ^ 2 * (hA.eigenvalues (eA i) * hB.eigenvalues j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hSapply, hmuA, hnuB]
    rfl
  rw [hreindex]
  exact sum_bilinear_le_of_mem_doublyStochastic hmu hnu hSmem

/-- Existential form of **von Neumann's trace inequality**: for Hermitian `A`, `B` there exist
listings `mu`, `nu` of their eigenvalues, both in decreasing order, with
`Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
theorem exists_vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ mu nu : Fin d → ℝ,
      (∃ eA : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ eA) ∧
      (∃ eB : Equiv.Perm (Fin d), nu = hB.eigenvalues ∘ eB) ∧
      Antitone mu ∧ Antitone nu ∧ (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨eA, hEA⟩ := exists_antitone_eigenvalues_perm hA
  obtain ⟨eB, hEB⟩ := exists_antitone_eigenvalues_perm hB
  exact ⟨hA.eigenvalues ∘ eA, hB.eigenvalues ∘ eB, ⟨eA, rfl⟩, ⟨eB, rfl⟩, hEA, hEB,
    vonNeumann_trace_ineq hA hB rfl rfl hEA hEB⟩

end Zeta23Redux.LinAlg

