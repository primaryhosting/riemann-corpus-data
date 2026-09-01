import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
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

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten `1`-norm) of a complex square matrix: the sum of its singular
values, i.e. the sum of the square roots of the eigenvalues of `Mᴴ * M`. -/
noncomputable def traceNorm (M : Matrix n n ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i)

lemma eigenvalues_congr {M N : Matrix n n ℂ} (hM : M.IsHermitian) (hN : N.IsHermitian)
    (h : M = N) : hM.eigenvalues = hN.eigenvalues := by
  subst h; rfl

/-- The eigenvalue multiset of `cfc f A` is the image under `f` of the eigenvalue multiset of the
Hermitian matrix `A`; consequently any symmetric sum transfers. -/
lemma sum_eigenvalues_cfc (f : ℝ → ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : (cfc f A).IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (hB.eigenvalues i) = ∑ i, g (f (hA.eigenvalues i)) := by
  have h1 : (cfc f A).charpoly.roots
      = Multiset.map (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) Finset.univ.val := by
    rw [hA.charpoly_cfc_eq f, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h2 := hB.roots_charpoly_eq_eigenvalues
  rw [h1] at h2
  have h3 : Multiset.map (fun i => hB.eigenvalues i) Finset.univ.val
      = Multiset.map (fun i => f (hA.eigenvalues i)) Finset.univ.val := by
    apply Multiset.map_injective (f := (fun x : ℝ => (x : ℂ))) Complex.ofReal_injective
    simp only [Multiset.map_map]
    exact h2.symm
  have h4 := congrArg (fun m => (Multiset.map g m).sum) h3
  simp only [Multiset.map_map] at h4
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact h4

lemma isHermitian_cfc (f : ℝ → ℝ) (A : Matrix n n ℂ) : (cfc f A).IsHermitian :=
  cfc_predicate (R := ℝ) f A

lemma cfc_sq_eq_mul_self {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun x : ℝ => x ^ 2) A = A * A := by
  have hsa : IsSelfAdjoint A := hA
  rw [← pow_two A, ← cfc_pow_id (R := ℝ) A 2 hsa]

/-- For a Hermitian matrix the trace norm is the sum of the absolute values of the eigenvalues. -/
lemma traceNorm_of_isHermitian {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    traceNorm M = ∑ i, |hM.eigenvalues i| := by
  have hcfc : (cfc (fun x : ℝ => x ^ 2) M).IsHermitian := isHermitian_cfc _ _
  have hsq : Mᴴ * M = cfc (fun x : ℝ => x ^ 2) M := by
    rw [cfc_sq_eq_mul_self hM, hM.eq]
  have hev := eigenvalues_congr (Matrix.isHermitian_conjTranspose_mul_self M) hcfc hsq
  rw [traceNorm, hev, sum_eigenvalues_cfc (fun x : ℝ => x ^ 2) hM hcfc Real.sqrt]
  simp [Real.sqrt_sq_eq_abs]

/-- Trace norm of a function of a Hermitian matrix, in terms of the eigenvalues. -/
lemma traceNorm_cfc (f : ℝ → ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (cfc f A) = ∑ i, |f (hA.eigenvalues i)| := by
  rw [traceNorm_of_isHermitian (isHermitian_cfc f A)]
  exact sum_eigenvalues_cfc f hA (isHermitian_cfc f A) (fun x => |x|)

lemma cfc_cos_sub_one (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    cfc (fun x : ℝ => Real.cos x - 1) A = cfc Real.cos A - 1 := by
  have hsa : IsSelfAdjoint A := hA
  rw [cfc_sub (R := ℝ) Real.cos (fun _ => 1) A (by fun_prop) (by fun_prop)]
  congr 1
  exact cfc_const_one ℝ A

/-- The trace of a Hermitian matrix is bounded in absolute value by its trace norm. -/
lemma norm_trace_le_traceNorm {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ‖M.trace‖ ≤ traceNorm M := by
  rw [hM.trace_eq_sum_eigenvalues, traceNorm_of_isHermitian hM]
  refine le_trans (norm_sum_le _ _) ?_
  exact le_of_eq (by simp)

/-- **Cos Trace Norm 2707.**  For every Hermitian complex matrix `A`, writing `cos A` for the
continuous functional calculus of `Real.cos` at `A`:

* the trace norm of `cos A` is at most the size of the matrix;
* `cos A` differs from the identity by at most `‖A * A‖₁ / 2` in trace norm;
* the trace of `cos A` is dominated in absolute value by the trace norm of `cos A`. -/
theorem CosTraceNorm2707 {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (cfc Real.cos A) ≤ (Fintype.card n : ℝ) ∧
    traceNorm (cfc Real.cos A - 1) ≤ traceNorm (A * A) / 2 ∧
    ‖(cfc Real.cos A).trace‖ ≤ traceNorm (cfc Real.cos A) := by
  refine ⟨?_, ?_, norm_trace_le_traceNorm (isHermitian_cfc Real.cos A)⟩
  · rw [traceNorm_cfc Real.cos hA]
    calc ∑ i, |Real.cos (hA.eigenvalues i)| ≤ ∑ _i : n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
      _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]
  · rw [← cfc_cos_sub_one A hA, traceNorm_cfc _ hA, ← cfc_sq_eq_mul_self hA,
      traceNorm_cfc _ hA, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : Real.cos (hA.eigenvalues i) ≤ 1 := Real.cos_le_one _
    have h2 : 1 - (hA.eigenvalues i) ^ 2 / 2 ≤ Real.cos (hA.eigenvalues i) :=
      Real.one_sub_sq_div_two_le_cos
    have h3 : |(hA.eigenvalues i) ^ 2| = (hA.eigenvalues i) ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [abs_of_nonpos (by linarith), h3]
    linarith

end Brockian

