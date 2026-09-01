import Mathlib

/-!
# Uhlmann's theorem

For positive semidefinite matrices `ρ σ : Matrix n n ℂ` (density operators, not necessarily
normalized), the fidelity

`F(ρ, σ) = Tr √(√ρ σ √ρ)`

equals the maximum of `|⟪ψ, φ⟫|` over all purifications `ψ` of `ρ` and `φ` of `σ` in
`ℂⁿ ⊗ ℂⁿ ≃ EuclideanSpace ℂ (n × n)`, where the reduced density matrix of a vector `ψ` is
the partial trace over the second tensor factor.

The main result is `QI.uhlmann_fidelity`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped ComplexOrder InnerProductSpace MatrixOrder

namespace QI

variable {n m : Type*} [Fintype n] [Fintype m]

/-! ### Vectorization of matrices -/

/-- The vectorization of a matrix, viewed as a vector of the Hilbert space
`EuclideanSpace ℂ (n × m) ≃ ℂⁿ ⊗ ℂᵐ`. -/
noncomputable def toVec (A : Matrix n m ℂ) : EuclideanSpace ℂ (n × m) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

/-- The matrix corresponding to a vector of `EuclideanSpace ℂ (n × m)`. -/
noncomputable def ofVec (ψ : EuclideanSpace ℂ (n × m)) : Matrix n m ℂ :=
  Matrix.of fun i k => ψ (i, k)

omit [Fintype n] [Fintype m] in
@[simp] lemma toVec_apply (A : Matrix n m ℂ) (p : n × m) : toVec A p = A p.1 p.2 := rfl

omit [Fintype n] [Fintype m] in
@[simp] lemma toVec_ofVec (ψ : EuclideanSpace ℂ (n × m)) : toVec (ofVec ψ) = ψ := by
  ext p; simp [toVec, ofVec]

lemma inner_toVec (A B : Matrix n m ℂ) : ⟪toVec A, toVec B⟫_ℂ = (Aᴴ * B).trace := by
  simp only [toVec, PiLp.inner_apply, Matrix.trace, Matrix.mul_apply, Matrix.diag,
    RCLike.inner_apply, Matrix.conjTranspose_apply]
  show ∑ p : n × m, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [mul_comm]

lemma norm_toVec_sq (A : Matrix n m ℂ) : ‖toVec A‖ ^ 2 = (Aᴴ * A).trace.re := by
  rw [← inner_toVec A A, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Cauchy–Schwarz for the Hilbert–Schmidt (Frobenius) inner product. -/
lemma norm_trace_conjTranspose_mul_le (A B : Matrix n m ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ ‖toVec A‖ * ‖toVec B‖ := by
  rw [← inner_toVec]
  exact norm_inner_le_norm _ _

/-! ### Purifications -/

/-- The reduced density matrix (partial trace over the second tensor factor) of a vector. -/
noncomputable def reduced (ψ : EuclideanSpace ℂ (n × m)) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k, ψ (i, k) * star (ψ (j, k))

/-- `ψ` is a purification of `ρ` if the partial trace of `ψ` over the ancilla is `ρ`. -/
def IsPurification (ψ : EuclideanSpace ℂ (n × m)) (ρ : Matrix n n ℂ) : Prop := reduced ψ = ρ

omit [Fintype n] in
lemma reduced_toVec (A : Matrix n m ℂ) : reduced (toVec A) = A * Aᴴ := by
  ext i j; simp [reduced, Matrix.mul_apply]

omit [Fintype n] in
lemma isPurification_toVec_iff (A : Matrix n m ℂ) (ρ : Matrix n n ℂ) :
    IsPurification (toVec A) ρ ↔ A * Aᴴ = ρ := by
  rw [IsPurification, reduced_toVec]

/-! ### Existence of unitaries -/

variable [DecidableEq n]

private lemma toEuclideanLin_mul_apply (A B : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- If `X Xᴴ = Y Yᴴ` then `X = Y U` for some unitary `U`. -/
theorem exists_unitary_of_mul_conjTranspose_eq {X Y : Matrix n n ℂ} (h : X * Xᴴ = Y * Yᴴ) :
    ∃ U : Matrix n n ℂ, U ∈ unitary (Matrix n n ℂ) ∧ X = Y * U := by
  classical
  let f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin Yᴴ
  let g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin Xᴴ
  have hinner : ∀ (Z : Matrix n n ℂ) (v : EuclideanSpace ℂ n),
      ⟪Matrix.toEuclideanLin Zᴴ v, Matrix.toEuclideanLin Zᴴ v⟫_ℂ
        = ⟪v, Matrix.toEuclideanLin (Z * Zᴴ) v⟫_ℂ := by
    intro Z v
    nth_rewrite 1 [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [LinearMap.adjoint_inner_left, toEuclideanLin_mul_apply]
  -- `Yᴴ` and `Xᴴ` have the same "norm profile"
  have hnorm : ∀ v, ‖g v‖ = ‖f v‖ := by
    intro v
    have h1 : ⟪g v, g v⟫_ℂ = ⟪f v, f v⟫_ℂ := by
      show ⟪Matrix.toEuclideanLin Xᴴ v, _⟫_ℂ = _
      rw [hinner X v, hinner Y v, h]
    have h2 : ‖g v‖ ^ 2 = ‖f v‖ ^ 2 := by
      have h3 := congrArg Complex.re h1
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
      exact_mod_cast h3
    nlinarith [norm_nonneg (g v), norm_nonneg (f v)]
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro v hv
    simp only [LinearMap.mem_ker] at hv ⊢
    have hv' := hnorm v
    rw [hv, norm_zero] at hv'
    exact norm_eq_zero.mp hv'
  -- the isometry `f v ↦ g v` defined on the range of `f`
  let L₀ : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ n :=
    ((LinearMap.ker f).liftQ g hker).comp
      (f.quotKerEquivRange.symm : (LinearMap.range f) →ₗ[ℂ] _)
  have hL₀ : ∀ v : EuclideanSpace ℂ n, L₀ ⟨f v, LinearMap.mem_range_self f v⟩ = g v := by
    intro v
    have hq : f.quotKerEquivRange (Submodule.Quotient.mk v)
        = ⟨f v, LinearMap.mem_range_self f v⟩ :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f v)
    show ((LinearMap.ker f).liftQ g hker) (f.quotKerEquivRange.symm _) = g v
    rw [← hq, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hiso : ∀ s : (LinearMap.range f), ‖L₀ s‖ = ‖s‖ := by
    rintro ⟨s, v, rfl⟩
    rw [hL₀ v]
    exact hnorm v
  let L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ n := ⟨L₀, hiso⟩
  -- extend it to an isometry of the whole space
  let T := L.extend
  have hT : ∀ v, T (Matrix.toEuclideanLin Yᴴ v) = Matrix.toEuclideanLin Xᴴ v := by
    intro v
    have := L.extend_apply ⟨f v, LinearMap.mem_range_self f v⟩
    simpa [T, L, hL₀ v] using this
  -- turn the isometry into a unitary matrix
  set Tm : Matrix n n ℂ := Matrix.toEuclideanLin.symm T.toLinearMap with hTmdef
  have hTm : ∀ v, Matrix.toEuclideanLin Tm v = T v := by
    intro v
    rw [hTmdef, LinearEquiv.apply_symm_apply]
    rfl
  have hone : Tmᴴ * Tm = 1 := by
    apply Matrix.toEuclideanLin.injective
    refine LinearMap.ext fun v => ?_
    rw [toEuclideanLin_mul_apply, hTm, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have hv : LinearMap.adjoint (Matrix.toEuclideanLin Tm) (T v) = v := by
      refine ext_inner_right ℂ fun w => ?_
      rw [LinearMap.adjoint_inner_left, hTm]
      exact T.inner_map_map v w
    rw [hv]
    simp
  have hone' : Tm * Tmᴴ = 1 := mul_eq_one_comm.mp hone
  have hXY : Tm * Yᴴ = Xᴴ := by
    apply Matrix.toEuclideanLin.injective
    refine LinearMap.ext fun v => ?_
    rw [toEuclideanLin_mul_apply, hTm]
    exact hT v
  refine ⟨Tmᴴ, ?_, ?_⟩
  · rw [Unitary.mem_iff]
    exact ⟨by simpa [star_eq_conjTranspose] using hone',
      by simpa [star_eq_conjTranspose] using hone⟩
  · rw [← Matrix.conjTranspose_conjTranspose X, ← hXY, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]

/-- Polar decomposition: every square matrix is a unitary times its absolute value. -/
theorem exists_unitary_polar (M : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, W ∈ unitary (Matrix n n ℂ) ∧ M = W * CFC.abs M := by
  have habs : (CFC.abs M).PosSemidef := (CFC.abs_nonneg M).posSemidef
  obtain ⟨U, hUu, hU⟩ := exists_unitary_of_mul_conjTranspose_eq (X := Mᴴ) (Y := CFC.abs M) (by
    rw [Matrix.conjTranspose_conjTranspose, habs.isHermitian, CFC.abs_mul_abs,
      star_eq_conjTranspose])
  refine ⟨Uᴴ, Unitary.star_mem hUu, ?_⟩
  conv_lhs => rw [← Matrix.conjTranspose_conjTranspose M, hU]
  rw [Matrix.conjTranspose_mul, habs.isHermitian]

/-! ### The trace bound -/

lemma posSemidef_abs (M : Matrix n n ℂ) : (CFC.abs M).PosSemidef := (CFC.abs_nonneg M).posSemidef

/-- For a positive semidefinite `P` and a unitary `U`, `|Tr (P U)| ≤ Tr P`. -/
lemma norm_trace_posSemidef_mul_unitary_le {P U : Matrix n n ℂ} (hP : P.PosSemidef)
    (hU : U ∈ unitary (Matrix n n ℂ)) : ‖(P * U).trace‖ ≤ P.trace.re := by
  have hUU' : U * Uᴴ = 1 := by simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hU).2
  set S : Matrix n n ℂ := CFC.sqrt P with hSdef
  have hS : S.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hSh : Sᴴ = S := hS.isHermitian
  have key : (P * U).trace = (Sᴴ * (S * U)).trace := by rw [hSh, ← Matrix.mul_assoc, hSS]
  have h1 : ‖toVec S‖ ^ 2 = P.trace.re := by rw [norm_toVec_sq, hSh, hSS]
  have h2 : ‖toVec (S * U)‖ ^ 2 = P.trace.re := by
    rw [norm_toVec_sq]
    congr 1
    rw [Matrix.conjTranspose_mul, hSh, Matrix.mul_assoc, ← Matrix.mul_assoc S S, hSS,
      Matrix.trace_mul_comm, Matrix.mul_assoc, hUU', Matrix.mul_one]
  have heq : ‖toVec S‖ = ‖toVec (S * U)‖ := by
    nlinarith [norm_nonneg (toVec S), norm_nonneg (toVec (S * U)), h1, h2]
  calc ‖(P * U).trace‖ = ‖(Sᴴ * (S * U)).trace‖ := by rw [key]
    _ ≤ ‖toVec S‖ * ‖toVec (S * U)‖ := norm_trace_conjTranspose_mul_le _ _
    _ = P.trace.re := by rw [← heq, ← sq, h1]

/-- For any square matrix `M` and unitary `W`, `|Tr (M W)| ≤ Tr |M|`. -/
lemma norm_trace_mul_unitary_le (M : Matrix n n ℂ) {W : Matrix n n ℂ}
    (hW : W ∈ unitary (Matrix n n ℂ)) : ‖(M * W).trace‖ ≤ (CFC.abs M).trace.re := by
  obtain ⟨W₀, hW₀u, hW₀⟩ := exists_unitary_polar M
  have key : (M * W).trace = (CFC.abs M * (W * W₀)).trace := by
    conv_lhs => rw [hW₀]
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [key]
  exact norm_trace_posSemidef_mul_unitary_le (posSemidef_abs M) (mul_mem hW hW₀u)

/-! ### Fidelity -/

/-- The fidelity `F(ρ, σ) = Tr √(√ρ σ √ρ)` of two positive semidefinite matrices. -/
noncomputable def fidelity (ρ σ : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace.re

lemma fidelity_eq_trace_abs (ρ : Matrix n n ℂ) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    fidelity ρ σ = (CFC.abs (CFC.sqrt σ * CFC.sqrt ρ)).trace.re := by
  rw [fidelity]
  congr 2
  rw [CFC.abs, star_eq_conjTranspose, Matrix.conjTranspose_mul,
    (CFC.sqrt_nonneg ρ).posSemidef.isHermitian, (CFC.sqrt_nonneg σ).posSemidef.isHermitian]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt σ),
    CFC.sqrt_mul_sqrt_self σ hσ.nonneg]

/-- Sanity check: the fidelity of a state with itself is its trace. -/
lemma fidelity_self {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) : fidelity ρ ρ = ρ.trace.re := by
  have hsq : CFC.sqrt ρ * ρ * CFC.sqrt ρ = ρ ^ 2 := by
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg,
      ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, sq]
  rw [fidelity, hsq, CFC.sqrt_sq ρ hρ.nonneg]

/-- **Uhlmann's theorem**: the fidelity of two positive semidefinite matrices `ρ`, `σ` is the
maximum of the overlap `|⟪ψ, φ⟫|` taken over all purifications `ψ` of `ρ` and `φ` of `σ`
(with an ancilla of the same dimension). -/
theorem uhlmann_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ ψ φ : EuclideanSpace ℂ (n × n),
      IsPurification ψ ρ ∧ IsPurification φ σ ∧ x = ‖⟪ψ, φ⟫_ℂ‖} (fidelity ρ σ) := by
  set R : Matrix n n ℂ := CFC.sqrt ρ with hRdef
  set S : Matrix n n ℂ := CFC.sqrt σ with hSdef
  have hR : R.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hS : S.PosSemidef := (CFC.sqrt_nonneg σ).posSemidef
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  have hRh : Rᴴ = R := hR.isHermitian
  have hSh : Sᴴ = S := hS.isHermitian
  set M : Matrix n n ℂ := S * R with hMdef
  have habs : (CFC.abs M).PosSemidef := posSemidef_abs M
  have hfid : fidelity ρ σ = (CFC.abs M).trace.re := fidelity_eq_trace_abs ρ hσ
  obtain ⟨W, hWu, hW⟩ := exists_unitary_polar M
  have hWW : Wᴴ * W = 1 := by
    simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hWu).1
  have hWW' : W * Wᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hWu).2
  have htr_nonneg : ‖(CFC.abs M).trace‖ = (CFC.abs M).trace.re := by
    have h0 : (0 : ℂ) ≤ (CFC.abs M).trace := habs.trace_nonneg
    rw [Complex.eq_re_of_ofReal_le h0] at *
    simp [Complex.norm_real, abs_of_nonneg (by exact_mod_cast h0 : (0:ℝ) ≤ (CFC.abs M).trace.re)]
  constructor
  · -- the value is attained
    refine ⟨toVec (R * Wᴴ), toVec S, ?_, ?_, ?_⟩
    · rw [isPurification_toVec_iff]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRh]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W R, hWW, Matrix.one_mul, hRR]
    · rw [isPurification_toVec_iff, hSh, hSS]
    · rw [inner_toVec]
      have hstar : ((R * Wᴴ)ᴴ * S) = W * (R * S) := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRh, Matrix.mul_assoc]
      rw [hstar, hfid]
      have h1 : ((W * (R * S))ᴴ).trace = (M * Wᴴ).trace := by
        congr 1
        rw [hMdef]
        simp [Matrix.conjTranspose_mul, hRh, hSh, Matrix.mul_assoc]
      have h2 : (M * Wᴴ).trace = (CFC.abs M).trace := by
        conv_lhs => rw [hW]
        rw [Matrix.trace_mul_cycle, hWW, Matrix.one_mul]
      have h3 : ‖(W * (R * S)).trace‖ = ‖(CFC.abs M).trace‖ := by
        rw [← h2, ← h1, Matrix.trace_conjTranspose, norm_star]
      rw [h3, htr_nonneg]
  · -- the value is an upper bound
    rintro x ⟨ψ, φ, hψ, hφ, rfl⟩
    set A : Matrix n n ℂ := ofVec ψ with hA
    set B : Matrix n n ℂ := ofVec φ with hB
    have hψA : ψ = toVec A := (toVec_ofVec ψ).symm
    have hφB : φ = toVec B := (toVec_ofVec φ).symm
    have hAA : A * Aᴴ = ρ := by rw [← isPurification_toVec_iff, ← hψA]; exact hψ
    have hBB : B * Bᴴ = σ := by rw [← isPurification_toVec_iff, ← hφB]; exact hφ
    obtain ⟨U, hUu, hU⟩ := exists_unitary_of_mul_conjTranspose_eq (X := A) (Y := R)
      (by rw [hAA, ← hRR]; nth_rewrite 2 [← hRh]; rfl)
    obtain ⟨V, hVu, hV⟩ := exists_unitary_of_mul_conjTranspose_eq (X := B) (Y := S)
      (by rw [hBB, ← hSS]; nth_rewrite 2 [← hSh]; rfl)
    rw [hψA, hφB, inner_toVec, hfid]
    have key : ‖(Aᴴ * B).trace‖ = ‖(M * (U * Vᴴ)).trace‖ := by
      have h1 : (Aᴴ * B)ᴴ = Vᴴ * (S * R) * U := by
        rw [hU, hV]
        simp [Matrix.conjTranspose_mul, hRh, hSh, Matrix.mul_assoc]
      have h2 : (Vᴴ * (S * R) * U).trace = (M * (U * Vᴴ)).trace := by
        rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm, hMdef]
      rw [← h2, ← h1, Matrix.trace_conjTranspose, norm_star]
    rw [key]
    exact norm_trace_mul_unitary_le M (mul_mem hUu (Unitary.star_mem hVu))

end QI

import Mathlib
import RequestProject.Uhlmann

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

