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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- Two antitone functions monovary. -/
lemma monovary_of_antitone {mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu) :
    Monovary mu nu := by
  intro i j hij
  rcases le_or_gt i j with h | h
  · exact absurd (hnu h) (not_le.mpr hij)
  · exact hmu h.le

/-- Rearrangement inequality in the form we need: pairing two antitone sequences in order is
optimal. -/
lemma sum_mul_comp_perm_le {mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu)
    (τ : Equiv.Perm (Fin d)) : ∑ i, mu i * nu (τ i) ≤ ∑ i, mu i * nu i := by
  have := (monovary_of_antitone hmu hnu).sum_smul_comp_perm_le_sum_smul (σ := τ)
  simpa [smul_eq_mul] using this

/-- If `mu`, `nu` are antitone reorderings of `a`, `b`, then any permuted pairing of `a` with `b`
is dominated by the sorted pairing. -/
lemma sum_perm_le {a b mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu)
    (pa pb : Equiv.Perm (Fin d)) (hma : mu = a ∘ pa) (hnb : nu = b ∘ pb)
    (σ : Equiv.Perm (Fin d)) : ∑ i, a i * b (σ i) ≤ ∑ i, mu i * nu i := by
  set τ : Equiv.Perm (Fin d) := pa.trans (σ.trans pb.symm) with hτ
  have key : ∑ i, a i * b (σ i) = ∑ k, mu k * nu (τ k) := by
    rw [← Equiv.sum_comp pa fun i => a i * b (σ i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : mu k = a (pa k) := by rw [hma]; rfl
    have h2 : nu (τ k) = b (σ (pa k)) := by rw [hnb]; simp [hτ]
    rw [h1, h2]
  rw [key]
  exact sum_mul_comp_perm_le hmu hnu τ

/-- The bilinear pairing of `a` and `b` against a doubly stochastic matrix is bounded by the
sorted pairing.  This is the Birkhoff step: a doubly stochastic matrix is a convex combination
of permutation matrices, and a linear functional bounded on the permutation matrices is bounded
on their convex hull. -/
lemma sum_doublyStochastic_le {a b mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu)
    (pa pb : Equiv.Perm (Fin d)) (hma : mu = a ∘ pa) (hnb : nu = b ∘ pb)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S ∈ doublyStochastic ℝ (Fin d)) :
    ∑ i, ∑ j, a i * b j * S i j ≤ ∑ i, mu i * nu i := by
  set c : ℝ := ∑ i, mu i * nu i with hc
  set f : Matrix (Fin d) (Fin d) ℝ → ℝ := fun M => ∑ i, ∑ j, a i * b j * M i j with hf
  have hlin : IsLinearMap ℝ f := by
    constructor
    · intro M N
      simp only [hf, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    · intro r M
      simp only [hf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hconv : Convex ℝ {M : Matrix (Fin d) (Fin d) ℝ | f M ≤ c} := convex_halfSpace_le hlin c
  have hsub : {x : Matrix (Fin d) (Fin d) ℝ | ∃ σ, Equiv.Perm.permMatrix ℝ σ = x} ⊆
      {M : Matrix (Fin d) (Fin d) ℝ | f M ≤ c} := by
    rintro _ ⟨σ, rfl⟩
    have hval : f (Equiv.Perm.permMatrix ℝ σ) = ∑ i, a i * b (σ i) := by
      simp [hf, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    show f _ ≤ c
    rw [hval]
    exact sum_perm_le hmu hnu pa pb hma hnb σ
  have h := convexHull_min hsub hconv
  rw [← doublyStochastic_eq_convexHull_permMatrix] at h
  exact h hS

/-- `z * star z` is the squared norm of `z`. -/
lemma mul_star_eq_normSq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq z

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
lemma normSq_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun i j => ‖W i j‖ ^ 2) ∈ doublyStochastic ℝ (Fin d) := by
  have h1 : star W * W = 1 := hW.1
  have h2 : W * star W = 1 := hW.2
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by simp, fun i => ?_, fun j => ?_⟩
  · have hi := congrFun (congrFun h2 i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hi
    have hcast : ((∑ j, ‖W i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← hi]
      exact Finset.sum_congr rfl fun j _ => (mul_star_eq_normSq (W i j)).symm
    exact_mod_cast hcast
  · have hj := congrFun (congrFun h1 j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hj
    have hcast : ((∑ i, ‖W i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← hj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
      exact (mul_star_eq_normSq (W i j)).symm
    exact_mod_cast hcast

/-- Trace of `diagonal a * W * diagonal b * star W` in terms of squared moduli of the entries
of `W`. -/
lemma trace_diag_conj (a b : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.diagonal (fun i => (a i : ℂ)) * W * Matrix.diagonal (fun j => (b j : ℂ)) * star W).trace
      = ((∑ i, ∑ j, a i * b j * ‖W i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_sum]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    mul_ite, mul_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, ← mul_star_eq_normSq]
  ring

/-- **Von Neumann's trace inequality** for Hermitian complex matrices: if `mu` and `nu` list the
eigenvalues of the Hermitian matrices `A` and `B` in the same (decreasing) order, then
`Re (tr (A * B)) ≤ ∑ i, mu i * nu i`.

The proof diagonalises both matrices, reduces the trace to a bilinear form against the entrywise
squared modulus of a unitary matrix — which is doubly stochastic — and then concludes by
Birkhoff's theorem together with the rearrangement inequality. -/
theorem vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {mu nu : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu)
    (pa pb : Equiv.Perm (Fin d))
    (hmuA : mu = hA.eigenvalues ∘ pa) (hnuB : nu = hB.eigenvalues ∘ pb) :
    (A * B).trace.re ≤ ∑ i, mu i * nu i := by
  set a := hA.eigenvalues with ha
  set b := hB.eigenvalues with hb
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hV
  set Da : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)) with hDa
  set Db : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun i => ((b i : ℝ) : ℂ)) with hDb
  have hAeq : A = U * Da * star U := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [hU, hDa, ha, Function.comp_def]
  have hBeq : B = V * Db * star V := by
    conv_lhs => rw [hB.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [hV, hDb, hb, Function.comp_def]
  set W : Matrix (Fin d) (Fin d) ℂ := star U * V with hW
  have hWu : W ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    have hUu : U ∈ Matrix.unitaryGroup (Fin d) ℂ := hA.eigenvectorUnitary.2
    have hVu : V ∈ Matrix.unitaryGroup (Fin d) ℂ := hB.eigenvectorUnitary.2
    exact mul_mem (Unitary.star_mem hUu) hVu
  have hstarW : star W = star V * U := by
    rw [hW, Matrix.star_mul, star_star]
  have htr : (A * B).trace = (Da * W * Db * star W).trace := by
    rw [hAeq, hBeq]
    rw [show U * Da * star U * (V * Db * star V) = U * (Da * star U * V * Db * star V) by
      noncomm_ring]
    rw [Matrix.trace_mul_comm]
    congr 1
    rw [hstarW, hW]
    noncomm_ring
  rw [htr, trace_diag_conj a b W, Complex.ofReal_re]
  exact sum_doublyStochastic_le hmu hnu pa pb hmuA hnuB (normSq_mem_doublyStochastic hWu)

/-- Any finite family of reals can be listed in decreasing order, so the hypotheses of
`vonNeumann_trace_ineq` are always satisfiable. -/
lemma exists_antitone_reindex (f : Fin d → ℝ) : ∃ p : Equiv.Perm (Fin d), Antitone (f ∘ p) := by
  refine ⟨Tuple.sort fun i => -f i, ?_⟩
  have h := Tuple.monotone_sort fun i => -f i
  intro i j hij
  have hij' := h hij
  simp only [Function.comp_apply] at hij' ⊢
  linarith

end Zeta23Redux.LinAlg

