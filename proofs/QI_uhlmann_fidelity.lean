import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Extending a partial isometry -/

/-- If `‖p x‖ = ‖m x‖` for all `x`, then the assignment `p x ↦ m x` extends to a global
linear isometry `w` of the (finite dimensional) space, i.e. `w (p x) = m x` for all `x`. -/
lemma exists_isometry_of_norm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (p m : E →ₗ[ℂ] E) (h : ∀ x, ‖p x‖ = ‖m x‖) :
    ∃ w : E →ₗᵢ[ℂ] E, ∀ x, w (p x) = m x := by
  have hker : LinearMap.ker p ≤ LinearMap.ker m := by
    intro x hx
    have hx' : p x = 0 := hx
    have hn := h x
    rw [hx', norm_zero] at hn
    exact LinearMap.mem_ker.mpr (by simpa using (norm_eq_zero.mp hn.symm))
  set g : (E ⧸ LinearMap.ker p) →ₗ[ℂ] E := (LinearMap.ker p).liftQ m hker with hg
  set L0 : (LinearMap.range p) →ₗ[ℂ] E := g ∘ₗ (p.quotKerEquivRange.symm : _ →ₗ[ℂ] _) with hL0def
  have hL0 : ∀ x : E, L0 ⟨p x, ⟨x, rfl⟩⟩ = m x := by
    intro x
    simp only [hL0def, LinearMap.coe_comp, Function.comp_apply]
    rw [LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    simp [hg]
  have hnorm : ∀ y : (LinearMap.range p), ‖L0 y‖ = ‖y‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hL0 x]
    simpa using (h x).symm
  let L : (LinearMap.range p) →ₗᵢ[ℂ] E := ⟨L0, hnorm⟩
  refine ⟨L.extend, fun x => ?_⟩
  have h1 := LinearIsometry.extend_apply L ⟨p x, ⟨x, rfl⟩⟩
  simpa [L, hL0 x] using h1

/-! ## Polar decomposition of a square complex matrix -/

lemma toEuclideanLin_mul' (A B : Matrix n n ℂ) : Matrix.toEuclideanLin (A * B) =
    (Matrix.toEuclideanLin A) ∘ₗ (Matrix.toEuclideanLin B) := toLpLin_mul 2 2 2 A B

lemma norm_sq_toEuclideanLin (M : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin M x‖ ^ 2 = (inner ℂ x (Matrix.toEuclideanLin (Mᴴ * M) x)).re := by
  rw [toEuclideanLin_mul', Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.comp_apply, LinearMap.adjoint_inner_right, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

/-- **Polar decomposition**: every square complex matrix factors as `M = U * √(Mᴴ M)` with
`U` unitary. -/
lemma exists_unitary_polar (M : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ M = U * CFC.sqrt (Mᴴ * M) := by
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hMM : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hP : P.PosSemidef := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  have hPP : Pᴴ * P = Mᴴ * M := by
    rw [hP.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self (Mᴴ * M) (ha := hMM.nonneg)
  have hnorm : ∀ x : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanLin P x‖ = ‖Matrix.toEuclideanLin M x‖ := by
    intro x
    have h1 := norm_sq_toEuclideanLin P x
    have h2 := norm_sq_toEuclideanLin M x
    rw [hPP] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h1.trans h2.symm)
  obtain ⟨w, hw⟩ := exists_isometry_of_norm_eq _ _ hnorm
  have hunit : (Matrix.toEuclideanLin.symm w.toLinearMap)ᴴ *
      (Matrix.toEuclideanLin.symm w.toLinearMap) = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul', Matrix.toEuclideanLin_conjTranspose_eq_adjoint, toLpLin_one]
    refine LinearMap.ext fun x => ?_
    refine ext_inner_left ℂ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    simp only [LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    exact w.inner_map_map y x
  refine ⟨Matrix.toEuclideanLin.symm w.toLinearMap, hunit, mul_eq_one_comm.mp hunit, ?_⟩
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul']
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply]
  exact (hw x).symm

/-- Left polar decomposition: `M = √(M Mᴴ) * U` with `U` unitary. -/
lemma exists_unitary_polar_left (M : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ M = CFC.sqrt (M * Mᴴ) * U := by
  obtain ⟨U, h1, h2, h3⟩ := exists_unitary_polar Mᴴ
  rw [Matrix.conjTranspose_conjTranspose] at h3
  refine ⟨Uᴴ, by simpa using h2, by simpa using h1, ?_⟩
  have h4 := congrArg Matrix.conjTranspose h3
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    ((CFC.sqrt_nonneg (M * Mᴴ)).posSemidef :
      (CFC.sqrt (M * Mᴴ) : Matrix n n ℂ).PosSemidef).isHermitian.eq] at h4
  exact h4

/-- Every matrix `A` with `A Aᴴ = ρ` is of the form `√ρ * U` with `U` unitary; conversely all
such matrices satisfy `A Aᴴ = ρ` when `ρ` is positive semidefinite. -/
lemma exists_unitary_of_mul_conjTranspose_eq {ρ A : Matrix n n ℂ} (h : A * Aᴴ = ρ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ A = CFC.sqrt ρ * U := by
  obtain ⟨U, h1, h2, h3⟩ := exists_unitary_polar_left A
  exact ⟨U, h1, h2, by rwa [h] at h3⟩

/-! ## The Hilbert–Schmidt inner product and the trace bound -/

/-- Hilbert–Schmidt vectorisation of a matrix. -/
def vecHS (A : Matrix n n ℂ) : EuclideanSpace ℂ (n × n) := WithLp.toLp 2 (fun p => A p.1 p.2)

omit [DecidableEq n] in
lemma inner_vecHS (A B : Matrix n n ℂ) : inner ℂ (vecHS A) (vecHS B) = (Aᴴ * B).trace := by
  rw [PiLp.inner_apply]
  simp only [vecHS, Matrix.trace, Matrix.mul_apply, Matrix.diag_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, RCLike.inner_apply]
  rw [Finset.sum_comm]
  simp [RCLike.star_def, mul_comm]

omit [DecidableEq n] in
lemma norm_vecHS (A : Matrix n n ℂ) : ‖vecHS A‖ = Real.sqrt ((Aᴴ * A).trace.re) := by
  rw [← Real.sqrt_sq (norm_nonneg (vecHS A)), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_vecHS]
  rfl

omit [DecidableEq n] in
/-- Cauchy–Schwarz for the Hilbert–Schmidt (Frobenius) inner product on matrices. -/
lemma norm_trace_conjTranspose_mul_le (A B : Matrix n n ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ Real.sqrt ((Aᴴ * A).trace.re) * Real.sqrt ((Bᴴ * B).trace.re) := by
  rw [← inner_vecHS, ← norm_vecHS, ← norm_vecHS]
  exact norm_inner_le_norm (𝕜 := ℂ) (vecHS A) (vecHS B)

omit [DecidableEq n] in
lemma re_trace_nonneg {P : Matrix n n ℂ} (hP : P.PosSemidef) : 0 ≤ P.trace.re := by
  have h := hP.trace_nonneg
  rw [Complex.le_def] at h
  simpa using h.1

omit [DecidableEq n] in
lemma norm_trace_eq_re {P : Matrix n n ℂ} (hP : P.PosSemidef) : ‖P.trace‖ = P.trace.re := by
  have h := hP.trace_nonneg
  rw [Complex.le_def] at h
  simp only [Complex.zero_re, Complex.zero_im] at h
  rw [Complex.norm_def, Complex.normSq_apply, ← h.2]
  simp [Real.sqrt_mul_self h.1]

/-- If `P` is positive semidefinite and `V` is unitary then `|tr (V P)| ≤ tr P`. -/
lemma norm_trace_unitary_mul_le {P V : Matrix n n ℂ} (hP : P.PosSemidef) (hV : Vᴴ * V = 1) :
    ‖(V * P).trace‖ ≤ P.trace.re := by
  set S := CFC.sqrt P with hSdef
  have hS : S.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P (ha := hP.nonneg)
  have hSh : Sᴴ = S := hS.isHermitian.eq
  have key : (V * P).trace = (Sᴴ * (V * S)).trace := by
    rw [hSh, ← hSS, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  have h1 : (Sᴴ * S).trace = P.trace := by rw [hSh, hSS]
  have h2 : ((V * S)ᴴ * (V * S)).trace = P.trace := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V S, hV,
      Matrix.one_mul, hSh, hSS]
  have hcs := norm_trace_conjTranspose_mul_le S (V * S)
  rw [h1, h2] at hcs
  rw [key]
  calc ‖(Sᴴ * (V * S)).trace‖ ≤ Real.sqrt (P.trace.re) * Real.sqrt (P.trace.re) := hcs
    _ = P.trace.re := Real.mul_self_sqrt (re_trace_nonneg hP)

/-! ## Fidelity and Uhlmann's theorem -/

/-- The (Uhlmann) fidelity of two positive semidefinite matrices,
`F(ρ, σ) = tr √(√ρ σ √ρ)`. -/
def fidelity (ρ σ : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace.re

/-- Sanity check on the definition: `F(ρ, ρ) = tr ρ` (so `F(ρ, ρ) = 1` for a state `ρ`). -/
lemma fidelity_self {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) : fidelity ρ ρ = ρ.trace.re := by
  have hRR : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ (ha := hρ.nonneg)
  have h : CFC.sqrt ρ * ρ * CFC.sqrt ρ = ρ ^ 2 := by
    calc CFC.sqrt ρ * ρ * CFC.sqrt ρ
        = CFC.sqrt ρ * (CFC.sqrt ρ * CFC.sqrt ρ) * CFC.sqrt ρ := by rw [hRR]
      _ = (CFC.sqrt ρ * CFC.sqrt ρ) * (CFC.sqrt ρ * CFC.sqrt ρ) := by noncomm_ring
      _ = ρ ^ 2 := by rw [hRR, sq]
  rw [fidelity, h, CFC.sqrt_sq ρ (ha := hρ.nonneg)]

/-- **Uhlmann's theorem**.  For positive semidefinite `ρ σ : Matrix n n ℂ`, the fidelity
`F(ρ, σ) = tr √(√ρ σ √ρ)` is the maximum of the overlaps `|⟪ψ, φ⟫|` taken over all
purifications `ψ` of `ρ` and `φ` of `σ`.

A purification of `ρ` on `ℂⁿ ⊗ ℂⁿ` is encoded by its matrix of coefficients
`A : Matrix n n ℂ` (that is, `ψ = ∑ i j, A i j • (eᵢ ⊗ eⱼ)`); the condition that its reduced
state (the partial trace over the ancilla) equals `ρ` reads `A * Aᴴ = ρ`, and the overlap of
two such vectors is `⟪ψ, φ⟫ = tr (Aᴴ B)`. -/
theorem uhlmann_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ A B : Matrix n n ℂ,
      A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ x = ‖(Aᴴ * B).trace‖} (fidelity ρ σ) := by
  set R := CFC.sqrt ρ with hRdef
  set T := CFC.sqrt σ with hTdef
  have hR : R.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hT : T.PosSemidef := (CFC.sqrt_nonneg σ).posSemidef
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self ρ (ha := hρ.nonneg)
  have hTT : T * T = σ := CFC.sqrt_mul_sqrt_self σ (ha := hσ.nonneg)
  have hRh : Rᴴ = R := hR.isHermitian.eq
  have hTh : Tᴴ = T := hT.isHermitian.eq
  have hYY : (R * T) * (R * T)ᴴ = R * σ * R := by
    rw [Matrix.conjTranspose_mul, hRh, hTh, Matrix.mul_assoc, ← Matrix.mul_assoc T T R, hTT,
      ← Matrix.mul_assoc]
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_unitary_polar_left (R * T)
  rw [hYY] at hU3
  set P := CFC.sqrt (R * σ * R) with hPdef
  have hP : P.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hfid : fidelity ρ σ = P.trace.re := rfl
  constructor
  · refine ⟨R, T * Uᴴ, ?_, ?_, ?_⟩
    · rw [hRh, hRR]
    · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hTh, Matrix.mul_assoc,
        ← Matrix.mul_assoc Uᴴ U T, hU1, Matrix.one_mul, hTT]
    · have hRT : Rᴴ * (T * Uᴴ) = P := by
        rw [hRh, ← Matrix.mul_assoc, hU3, Matrix.mul_assoc, hU2, Matrix.mul_one]
      rw [hRT, hfid, norm_trace_eq_re hP]
  · rintro x ⟨A, B, hA, hB, rfl⟩
    obtain ⟨U₁, hU11, hU12, rfl⟩ := exists_unitary_of_mul_conjTranspose_eq hA
    obtain ⟨U₂, hU21, hU22, rfl⟩ := exists_unitary_of_mul_conjTranspose_eq hB
    rw [← hRdef, ← hTdef] at *
    have hV : ((U * (U₂ * U₁ᴴ))ᴴ) * (U * (U₂ * U₁ᴴ)) = 1 := by
      have h : (U * (U₂ * U₁ᴴ))ᴴ * (U * (U₂ * U₁ᴴ)) = U₁ * (U₂ᴴ * ((Uᴴ * U) * U₂) * U₁ᴴ) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        noncomm_ring
      rw [h, hU1, Matrix.one_mul, hU21, Matrix.one_mul, hU12]
    have htr : ((R * U₁)ᴴ * (T * U₂)).trace = ((U * (U₂ * U₁ᴴ)) * P).trace := by
      rw [Matrix.conjTranspose_mul, hRh]
      calc (U₁ᴴ * R * (T * U₂)).trace = (U₁ᴴ * ((R * T) * U₂)).trace := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = (U₁ᴴ * ((P * U) * U₂)).trace := by rw [hU3]
        _ = (((P * U) * U₂) * U₁ᴴ).trace := Matrix.trace_mul_comm _ _
        _ = (P * (U * (U₂ * U₁ᴴ))).trace := by
            rw [show (P * U) * U₂ * U₁ᴴ = P * (U * (U₂ * U₁ᴴ)) from by noncomm_ring]
        _ = ((U * (U₂ * U₁ᴴ)) * P).trace := Matrix.trace_mul_comm _ _
    rw [htr, hfid]
    exact norm_trace_unitary_mul_le hP hV

end

end QI

