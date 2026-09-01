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
open scoped Matrix

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

namespace Brockian

/-- The cosine Gram matrix `C θ i j = cos (θ i - θ j)`. -/
noncomputable def cosGram {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The `2 × n` matrix whose `i`-th column is the unit vector `(cos (θ i), sin (θ i))`. -/
noncomputable def cosFrame {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k i => if k = 0 then Real.cos (θ i) else Real.sin (θ i)

lemma cosGram_eq_conjTranspose_mul_self {n : ℕ} (θ : Fin n → ℝ) :
    cosGram θ = (cosFrame θ)ᴴ * cosFrame θ := by
  ext i j
  simp [cosGram, cosFrame, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub]

lemma cosGram_posSemidef {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma cosGram_isHermitian {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).IsHermitian :=
  (cosGram_posSemidef θ).isHermitian

lemma cosGram_trace {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 2707.**  The trace norm (sum of the absolute values of the
eigenvalues) of the cosine Gram matrix `i j ↦ cos (θ i - θ j)` equals its dimension `n`.
The matrix is positive semidefinite, being the Gram matrix of the unit vectors
`(cos (θ i), sin (θ i))`, so its trace norm coincides with its trace, which is `n`. -/
theorem CosTraceNorm2707 {n : ℕ} (θ : Fin n → ℝ)
    (hherm : (cosGram θ).IsHermitian) :
    ∑ i, |hherm.eigenvalues i| = (n : ℝ) := by
  have hpos : ∀ i, 0 ≤ hherm.eigenvalues i := fun i =>
    Matrix.PosSemidef.eigenvalues_nonneg (cosGram_posSemidef θ) i
  have h1 : ∑ i, |hherm.eigenvalues i| = ∑ i, hherm.eigenvalues i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hpos i)
  have h2 : (cosGram θ).trace = ∑ i, ((hherm.eigenvalues i : ℝ)) :=
    hherm.trace_eq_sum_eigenvalues
  rw [h1, ← h2, cosGram_trace]

end Brockian

