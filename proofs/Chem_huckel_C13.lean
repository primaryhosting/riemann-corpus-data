import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
(The `import Mathlib` line must precede the module docstring: Lean 4 requires all
`import` commands to appear at the very beginning of a file.)
-/

namespace Chem

open Matrix SimpleGraph Finset

/-- A primitive 13-th root of unity. -/
noncomputable def zt : ℂ := Complex.exp (2 * Real.pi * Complex.I / 13)

lemma zt_isPrimitiveRoot : IsPrimitiveRoot zt 13 := by
  have h := Complex.isPrimitiveRoot_exp 13 (by norm_num)
  simpa [zt] using h

lemma zt_pow_thirteen : zt ^ 13 = 1 := zt_isPrimitiveRoot.pow_eq_one

lemma zt_ne_zero : zt ≠ 0 := Complex.exp_ne_zero _

lemma zt_pow_mod (m : ℕ) : zt ^ (m % 13) = zt ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 13]
  rw [pow_add, pow_mul, zt_pow_thirteen, one_pow, one_mul]

/-- The character `k ↦ ζ^k` of `Fin 13` (viewed as `ℤ/13ℤ`). -/
noncomputable def ev (x : Fin 13) : ℂ := zt ^ x.val

lemma ev_add (x y : Fin 13) : ev (x + y) = ev x * ev y := by
  simp [ev, Fin.val_add, zt_pow_mod, pow_add]

lemma ev_ne_zero (x : Fin 13) : ev x ≠ 0 := pow_ne_zero _ zt_ne_zero

/-- The candidate eigenvalues. -/
noncomputable def lam (k : Fin 13) : ℂ := ev k + (ev k)⁻¹

lemma lam_eq_cos (k : Fin 13) :
    lam k = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 13) := by
  have hz : ev k = Complex.exp ((((2 * Real.pi * (k : ℕ) / 13 : ℝ)) : ℂ) * Complex.I) := by
    rw [ev, zt, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz' : (ev k)⁻¹ = Complex.exp (-((((2 * Real.pi * (k : ℕ) / 13 : ℝ)) : ℂ) * Complex.I)) := by
    rw [hz, ← Complex.exp_neg]
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 13 with ht
  rw [lam, hz, hz']
  have h1 : Complex.exp ((t : ℂ) * Complex.I) = Complex.cos t + Complex.sin t * Complex.I :=
    Complex.exp_mul_I
  have h2 : Complex.exp (-((t : ℂ) * Complex.I)) = Complex.cos (-t) + Complex.sin (-t) * Complex.I := by
    have := Complex.exp_mul_I (z := -(t : ℂ))
    rw [← this]; ring_nf
  rw [h1, h2, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  ring

/-- The Vandermonde-type matrix of characters; its columns are the eigenvectors. -/
noncomputable def F : Matrix (Fin 13) (Fin 13) ℂ := Matrix.vandermonde ev

lemma F_apply (i k : Fin 13) : F i k = ev (i * k) := by
  simp [F, Matrix.vandermonde_apply, ev, Fin.val_mul, zt_pow_mod, pow_mul]

lemma F_det_ne_zero : F.det ≠ 0 := by
  rw [F, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have : ev j ≠ ev i := by
    intro h
    have := zt_isPrimitiveRoot.pow_inj j.isLt i.isLt h
    exact absurd (Fin.ext this) (ne_of_gt hij)
  exact sub_ne_zero_of_ne this

/-- The adjacency matrix of the cycle graph `C₁₃`. -/
noncomputable def A : Matrix (Fin 13) (Fin 13) ℂ := (cycleGraph 13).adjMatrix ℂ

lemma A_mul_F : A * F = F * Matrix.diagonal lam := by
  ext i k
  have hne : ∀ i : Fin 13, i - 1 ≠ i + 1 := by decide
  have hsum : (A * F) i k = F (i - 1) k + F (i + 1) k := by
    have h1 : (A * F) i k = (A *ᵥ fun j => F j k) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, A, adjMatrix_mulVec_apply, cycleGraph_neighborFinset,
      Finset.sum_pair (hne i)]
  rw [hsum, Matrix.mul_diagonal, F_apply, F_apply, F_apply, lam]
  have e1 : ev ((i + 1) * k) = ev (i * k) * ev k := by
    rw [← ev_add]; ring_nf
  have e2 : ev ((i - 1) * k) * ev k = ev (i * k) := by
    rw [← ev_add]; ring_nf
  have e3 : ev ((i - 1) * k) = ev (i * k) * (ev k)⁻¹ := by
    field_simp [ev_ne_zero k] at e2 ⊢
    linear_combination e2
  rw [e1, e3]
  ring

lemma det_shift (mu : ℂ) :
    (Matrix.diagonal (fun _ : Fin 13 => mu) - A).det = ∏ k, (mu - lam k) := by
  have hc : ∀ M : Matrix (Fin 13) (Fin 13) ℂ,
      Matrix.diagonal (fun _ : Fin 13 => mu) * M = M * Matrix.diagonal (fun _ : Fin 13 => mu) := by
    intro M
    rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have key : (Matrix.diagonal (fun _ : Fin 13 => mu) - A) * F
      = F * Matrix.diagonal (fun k => mu - lam k) := by
    rw [sub_mul, A_mul_F, hc F, ← Matrix.diagonal_sub, Matrix.mul_sub]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ F_det_ne_zero (by linear_combination hdet :
    (Matrix.diagonal (fun _ : Fin 13 => mu) - A).det * F.det = (∏ k, (mu - lam k)) * F.det)
  exact this

/-- **Hückel theory for the cyclic polyene C₁₃H₁₃ (the cyclotridecatrienyl system).**
The eigenvalues of the adjacency matrix of the cycle graph `C₁₃` (i.e. the Hückel
matrix in units where `α = 0`, `β = 1`) are exactly the numbers
`2 cos (2πk/13)` for `k = 0, 1, …, 12`. -/
theorem huckel_C13 (mu : ℂ) :
    mu ∈ spectrum ℂ ((cycleGraph 13).adjMatrix ℂ) ↔
      ∃ k < 13, mu = 2 * Real.cos (2 * Real.pi * k / 13) := by
  have halg : (algebraMap ℂ (Matrix (Fin 13) (Fin 13) ℂ)) mu
      = Matrix.diagonal (fun _ : Fin 13 => mu) := by
    rw [Matrix.algebraMap_eq_diagonal]
    rfl
  rw [spectrum.mem_iff, halg, ← A, Matrix.isUnit_iff_isUnit_det, det_shift,
    isUnit_iff_ne_zero, not_ne_iff, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k.val, k.isLt, by rw [sub_eq_zero] at hk; rw [hk, ← lam_eq_cos k]⟩
  · rintro ⟨k, hk, hmu⟩
    refine ⟨⟨k, hk⟩, Finset.mem_univ _, ?_⟩
    rw [sub_eq_zero, hmu, lam_eq_cos ⟨k, hk⟩]

end Chem

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

