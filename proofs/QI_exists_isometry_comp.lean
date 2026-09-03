/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Module ComplexConjugate
open scoped MatrixOrder ComplexOrder

namespace QI

/-! ### Auxiliary results: isometries, polar decomposition -/

/-- If two linear endomorphisms of a finite-dimensional inner product space have pointwise
equal norms, then one is obtained from the other by composing with a linear isometry. -/
theorem exists_isometry_comp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (f g : V →ₗ[ℂ] V) (h : ∀ x, ‖g x‖ = ‖f x‖) :
    ∃ u : V →ₗᵢ[ℂ] V, ∀ x, u (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have : ‖g x‖ = 0 := by rw [h x]; simp [LinearMap.mem_ker.mp hx]
    simpa using norm_eq_zero.mp this
  set e := f.quotKerEquivRange with he
  set L₁ : (LinearMap.range f) →ₗ[ℂ] V :=
    ((LinearMap.ker f).liftQ g hker).comp
      (e.symm : (LinearMap.range f) →ₗ[ℂ] (V ⧸ LinearMap.ker f)) with hL₁
  have key : ∀ x : V, L₁ ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    have h1 : e (Submodule.Quotient.mk x) = ⟨f x, LinearMap.mem_range_self f x⟩ :=
      Subtype.ext (f.quotKerEquivRange_apply_mk x)
    rw [hL₁]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h1, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hnorm : ∀ y : (LinearMap.range f), ‖L₁ y‖ = ‖y‖ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    rw [key x]
    simpa using h x
  refine ⟨(⟨L₁, hnorm⟩ : (LinearMap.range f) →ₗᵢ[ℂ] V).extend, fun x => ?_⟩
  have := LinearIsometry.extend_apply (⟨L₁, hnorm⟩ : (LinearMap.range f) →ₗᵢ[ℂ] V)
    ⟨f x, LinearMap.mem_range_self f x⟩
  simpa [key x] using this

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two square matrices with the same Gram matrix differ by a unitary factor on the left. -/
theorem exists_unitary_of_gram (X Y : Matrix n n ℂ) (h : Xᴴ * X = Yᴴ * Y) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ X = U * Y := by
  have hin : ∀ (Z : Matrix n n ℂ) (v : EuclideanSpace ℂ n),
      (inner ℂ (Matrix.toEuclideanLin Z v) (Matrix.toEuclideanLin Z v) : ℂ)
        = inner ℂ v (Matrix.toEuclideanLin (Zᴴ * Z) v) := by
    intro Z v
    have h1 : Matrix.toEuclideanLin (Zᴴ * Z) v
        = Matrix.toEuclideanLin Zᴴ (Matrix.toEuclideanLin Z v) := by
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [h1, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
  have hnorm : ∀ v : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanLin X v‖ = ‖Matrix.toEuclideanLin Y v‖ := by
    intro v
    have hv : (inner ℂ (Matrix.toEuclideanLin X v) (Matrix.toEuclideanLin X v) : ℂ)
        = inner ℂ (Matrix.toEuclideanLin Y v) (Matrix.toEuclideanLin Y v) :=
      (hin X v).trans (by rw [h]; exact (hin Y v).symm)
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hv]
  obtain ⟨u, hu⟩ := exists_isometry_comp (Matrix.toEuclideanLin Y) (Matrix.toEuclideanLin X)
    (fun v => hnorm v)
  refine ⟨Matrix.toEuclideanLin.symm u.toLinearMap, ?_, ?_⟩
  · set U := Matrix.toEuclideanLin.symm u.toLinearMap with hU
    have hUL : Matrix.toEuclideanLin U = u.toLinearMap := by
      rw [hU, LinearEquiv.apply_symm_apply]
    have hcol : ∀ i : n, WithLp.toLp 2 (Uᵀ i) = u (EuclideanSpace.single i (1 : ℂ)) := by
      intro i
      have h2 : Matrix.toEuclideanLin U (EuclideanSpace.single i (1 : ℂ))
          = WithLp.toLp 2 (Uᵀ i) := by
        ext k
        simp [Matrix.toLpLin_apply]
      rw [← h2, hUL]; rfl
    ext i j
    rw [← inner_matrix_col_col, hcol i, hcol j, u.inner_map_map]
    simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, Matrix.one_apply]
  · apply Matrix.toEuclideanLin.injective
    ext1 v
    have hUL : Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) = u.toLinearMap :=
      LinearEquiv.apply_symm_apply _ _
    have h3 : Matrix.toEuclideanLin ((Matrix.toEuclideanLin.symm u.toLinearMap) * Y) v
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap)
            (Matrix.toEuclideanLin Y v) := by
      simp [Matrix.toLpLin_apply]
    rw [h3, hUL]
    exact (hu v).symm

/-- Polar decomposition: every square complex matrix `A` factors as `√(A Aᴴ) * U` with `U`
unitary. -/
theorem exists_polar_decomposition (A : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ A = CFC.sqrt (A * Aᴴ) * U := by
  have hpsd : (0 : Matrix n n ℂ) ≤ A * Aᴴ := (Matrix.posSemidef_self_mul_conjTranspose A).nonneg
  have hPh : (CFC.sqrt (A * Aᴴ))ᴴ = CFC.sqrt (A * Aᴴ) :=
    (CFC.sqrt_nonneg (A * Aᴴ)).posSemidef.isHermitian
  have hPP : CFC.sqrt (A * Aᴴ) * CFC.sqrt (A * Aᴴ) = A * Aᴴ := CFC.sqrt_mul_sqrt_self _ hpsd
  obtain ⟨U₀, hU₀, hAU⟩ := exists_unitary_of_gram Aᴴ (CFC.sqrt (A * Aᴴ)) (by
    rw [conjTranspose_conjTranspose, hPh, hPP])
  refine ⟨U₀ᴴ, by rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hU₀,
    by rw [conjTranspose_conjTranspose]; exact hU₀, ?_⟩
  have := congrArg conjTranspose hAU
  simpa [conjTranspose_mul, hPh] using this

/-! ### Vectorisation and the Frobenius (Hilbert–Schmidt) inner product -/

/-- Vectorisation of a matrix, viewed as an element of the Hilbert space `ℂ^(n × n)`. -/
noncomputable def vec (X : Matrix n n ℂ) : EuclideanSpace ℂ (n × n) :=
  WithLp.toLp 2 (fun p => X p.1 p.2)

omit [DecidableEq n] in
theorem inner_vec (X Y : Matrix n n ℂ) :
    (inner ℂ (vec X) (vec Y) : ℂ) = (Xᴴ * Y).trace := by
  simp only [vec, PiLp.inner_apply, RCLike.inner_apply, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Fintype.sum_prod_type]
  simp_rw [mul_comm]
  exact Finset.sum_comm

omit [DecidableEq n] in
theorem norm_vec_sq (X : Matrix n n ℂ) : ‖vec X‖ ^ 2 = (Xᴴ * X).trace.re := by
  have h := inner_self_nonneg (𝕜 := ℂ) (x := vec X)
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), Real.sq_sqrt h, inner_vec]
  rfl

/-! ### Trace norm and fidelity -/

/-- The trace norm (Schatten 1-norm) of a matrix: `‖M‖₁ = Tr √(Mᴴ M)`. -/
noncomputable def traceNorm (M : Matrix n n ℂ) : ℝ := (CFC.sqrt (Mᴴ * M)).trace.re

/-- The (Uhlmann) fidelity of two states: `F(ρ, σ) = Tr |√ρ √σ| = ‖√ρ √σ‖₁`. -/
noncomputable def fidelity (ρ σ : Matrix n n ℂ) : ℝ := traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

theorem traceNorm_nonneg (M : Matrix n n ℂ) : 0 ≤ traceNorm M :=
  (Complex.nonneg_iff.mp (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef.trace_nonneg).1

omit [DecidableEq n] in
/-- The trace of a positive semidefinite matrix is real. -/
theorem trace_ofReal_re {S : Matrix n n ℂ} (h : S.PosSemidef) :
    ((S.trace.re : ℝ) : ℂ) = S.trace := by
  have h0 : (0 : ℂ) ≤ S.trace := h.trace_nonneg
  exact Complex.ext (by simp) (by simp [← (Complex.nonneg_iff.mp h0).2])

private theorem trace_mul_unitary_aux (R U M : Matrix n n ℂ) (hU2 : U * Uᴴ = 1)
    (hM : M = Uᴴ * R) : (M * U).trace = R.trace := by
  conv_lhs => rw [hM]
  rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc, hU2, mul_one]

set_option maxHeartbeats 1000000 in
/-- Variational upper bound: `|Tr (V M)| ≤ ‖M‖₁` for every unitary `V`. -/
theorem norm_trace_unitary_mul_le (M V : Matrix n n ℂ) (hV : Vᴴ * V = 1) :
    ‖(V * M).trace‖ ≤ traceNorm M := by
  obtain ⟨U, hU1, hU2, hM⟩ := exists_polar_decomposition Mᴴ
  rw [conjTranspose_conjTranspose] at hM
  have hRpsd : (CFC.sqrt (Mᴴ * M)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hRh : (CFC.sqrt (Mᴴ * M))ᴴ = CFC.sqrt (Mᴴ * M) := hRpsd.isHermitian
  have hM' : M = Uᴴ * CFC.sqrt (Mᴴ * M) := by
    have h2 := congrArg conjTranspose hM
    rw [conjTranspose_conjTranspose, conjTranspose_mul, hRh] at h2
    exact h2
  set R := CFC.sqrt (Mᴴ * M) with hRdef
  set S := CFC.sqrt R with hSdef
  have hSpsd : S.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hSh : Sᴴ = S := hSpsd.isHermitian
  have hSS : S * S = R := CFC.sqrt_mul_sqrt_self R hRpsd.nonneg
  set G := V * Uᴴ with hGdef
  have hG : Gᴴ * G = 1 := by
    rw [hGdef, conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc, ← mul_assoc Vᴴ V Uᴴ,
      hV, one_mul, hU2]
  have key : (V * M).trace = (Sᴴ * (G * S)).trace := by
    have e1 : V * M = (G * S) * S := by
      rw [hM', ← hSS, hGdef]; noncomm_ring
    rw [e1, hSh, Matrix.trace_mul_comm]
  have hnS : ‖vec S‖ ^ 2 = traceNorm M := by
    rw [norm_vec_sq, hSh, hSS]; rfl
  have hnGS : ‖vec (G * S)‖ ^ 2 = traceNorm M := by
    rw [norm_vec_sq, conjTranspose_mul, mul_assoc, ← mul_assoc Gᴴ G S, hG, one_mul, hSh, hSS]; rfl
  have heq : ‖vec (G * S)‖ = ‖vec S‖ := by
    have h3 := hnGS.trans hnS.symm
    nlinarith [norm_nonneg (vec (G * S)), norm_nonneg (vec S)]
  rw [key, ← inner_vec]
  calc ‖(inner ℂ (vec S) (vec (G * S)) : ℂ)‖ ≤ ‖vec S‖ * ‖vec (G * S)‖ := norm_inner_le_norm _ _
    _ = traceNorm M := by rw [heq, ← sq, hnS]

set_option maxHeartbeats 1000000 in
/-- The upper bound is attained: there is a unitary `V` with `Tr (M V) = ‖M‖₁`. -/
theorem exists_unitary_trace_eq (M : Matrix n n ℂ) :
    ∃ V : Matrix n n ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧ (M * V).trace = (traceNorm M : ℂ) := by
  obtain ⟨U, hU1, hU2, hM⟩ := exists_polar_decomposition Mᴴ
  rw [conjTranspose_conjTranspose] at hM
  have hRh : (CFC.sqrt (Mᴴ * M))ᴴ = CFC.sqrt (Mᴴ * M) :=
    (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hM' : M = Uᴴ * CFC.sqrt (Mᴴ * M) := by
    have h2 := congrArg conjTranspose hM
    rw [conjTranspose_conjTranspose, conjTranspose_mul, hRh] at h2
    exact h2
  exact ⟨U, hU1, hU2, by
    rw [trace_mul_unitary_aux _ _ _ hU2 hM', traceNorm,
      trace_ofReal_re (CFC.sqrt_nonneg _).posSemidef]⟩

/-- Sanity check: the fidelity of a state with itself is its trace (`= 1` for density
matrices). -/
theorem fidelity_self {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) : fidelity ρ ρ = ρ.trace.re := by
  have h1 : ρᴴ * ρ = ρ ^ 2 := by rw [hρ.isHermitian.eq, sq]
  rw [fidelity, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, traceNorm, h1, CFC.sqrt_sq ρ]

/-! ### Purifications -/

/-- `ψ : n × n → ℂ`, a vector of the composite system `ℂ^n ⊗ ℂ^n`, is a purification of the
state `ρ` when tracing out the second (ancilla) factor of `|ψ⟩⟨ψ|` returns `ρ`. -/
def IsPurification (ρ : Matrix n n ℂ) (ψ : n × n → ℂ) : Prop :=
  ∀ i j, ∑ k, ψ (i, k) * conj (ψ (j, k)) = ρ i j

/-- The overlap `⟨ψ, φ⟩` of two vectors of the composite system. -/
noncomputable def overlap (ψ φ : n × n → ℂ) : ℂ := ∑ p, conj (ψ p) * φ p

omit [DecidableEq n] in
/-- Matrix form of a purification: `ψ` is a purification of `ρ` iff the associated matrix `A`
satisfies `A Aᴴ = ρ`. -/
theorem isPurification_iff (ρ : Matrix n n ℂ) (ψ : n × n → ℂ) :
    IsPurification ρ ψ ↔
      (Matrix.of fun i k => ψ (i, k)) * (Matrix.of fun i k => ψ (i, k))ᴴ = ρ := by
  constructor
  · intro h
    ext i j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h i j
  · intro h i j
    have := congrFun (congrFun (congrArg Matrix.of.symm h) i) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this

omit [DecidableEq n] in
theorem overlap_eq_trace (ψ φ : n × n → ℂ) :
    overlap ψ φ = ((Matrix.of fun i k => ψ (i, k))ᴴ * (Matrix.of fun i k => φ (i, k))).trace := by
  simp only [overlap, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-! ### Uhlmann's theorem -/

set_option maxHeartbeats 1000000 in
/-- Matrix form of Uhlmann's theorem. -/
theorem uhlmann_fidelity_matrix {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ A B : Matrix n n ℂ, A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧
      x = ‖(Aᴴ * B).trace‖} (fidelity ρ σ) := by
  have hPh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hQh : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hPP : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hQQ : CFC.sqrt σ * CFC.sqrt σ = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  set P := CFC.sqrt ρ with hPdef
  set Q := CFC.sqrt σ with hQdef
  constructor
  · obtain ⟨V, hV1, hV2, hVeq⟩ := exists_unitary_trace_eq (P * Q)
    refine ⟨P, Q * V, by rw [hPh, hPP], ?_, ?_⟩
    · rw [conjTranspose_mul, hQh]
      calc Q * V * (Vᴴ * Q) = Q * (V * Vᴴ) * Q := by noncomm_ring
        _ = σ := by rw [hV2, mul_one, hQQ]
    · have e : Pᴴ * (Q * V) = P * Q * V := by rw [hPh]; noncomm_ring
      rw [e, hVeq, Complex.norm_real, Real.norm_of_nonneg (traceNorm_nonneg _), fidelity,
        hPdef, hQdef]
  · rintro x ⟨A, B, hA, hB, rfl⟩
    obtain ⟨U₁, h11, h12, hA'⟩ := exists_polar_decomposition A
    obtain ⟨U₂, h21, h22, hB'⟩ := exists_polar_decomposition B
    rw [hA] at hA'
    rw [hB] at hB'
    have e : Aᴴ * B = (U₁ᴴ * (P * Q)) * U₂ := by
      rw [hA', hB', conjTranspose_mul, hPh]; noncomm_ring
    have e2 : U₂ * (U₁ᴴ * (P * Q)) = (U₂ * U₁ᴴ) * (P * Q) := by noncomm_ring
    rw [e, Matrix.trace_mul_comm, e2]
    refine norm_trace_unitary_mul_le _ _ ?_
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc U₁ * U₂ᴴ * (U₂ * U₁ᴴ) = U₁ * (U₂ᴴ * U₂) * U₁ᴴ := by noncomm_ring
      _ = 1 := by rw [h21, mul_one, h12]

/-- **Uhlmann's theorem**: the fidelity `F(ρ, σ) = Tr |√ρ √σ|` of two states is the maximum of
the modulus of the overlap `|⟨ψ, φ⟩|` taken over all purifications `ψ` of `ρ` and `φ` of `σ`. -/
theorem uhlmann_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ ψ φ : n × n → ℂ, IsPurification ρ ψ ∧ IsPurification σ φ ∧
      x = ‖overlap ψ φ‖} (fidelity ρ σ) := by
  obtain ⟨⟨A, B, hA, hB, hx⟩, hub⟩ := uhlmann_fidelity_matrix hρ hσ
  constructor
  · refine ⟨fun p => A p.1 p.2, fun p => B p.1 p.2, (isPurification_iff ρ _).mpr hA,
      (isPurification_iff σ _).mpr hB, ?_⟩
    rw [overlap_eq_trace]
    exact hx
  · rintro x ⟨ψ, φ, hψ, hφ, rfl⟩
    exact hub ⟨_, _, (isPurification_iff ρ ψ).mp hψ, (isPurification_iff σ φ).mp hφ,
      by rw [overlap_eq_trace]⟩

end QI

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

