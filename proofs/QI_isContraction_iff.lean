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

set_option grind.warning false

/-!
# Uhlmann's theorem

For positive semidefinite matrices `ρ σ : Matrix n n ℂ` (in particular, for density matrices of
a finite dimensional quantum system) the *fidelity* is

`F(ρ, σ) = tr √(√ρ σ √ρ)`.

A vector of `ℂ^n ⊗ ℂ^m` is encoded here as a matrix `A : Matrix n m ℂ`; its reduced density
matrix on the first factor is `A * Aᴴ`, and the overlap of the vectors encoded by `A` and `B` is
`tr (Aᴴ * B)`.  Thus `A` is a *purification* of `ρ` exactly when `A * Aᴴ = ρ`.

**Uhlmann's theorem** (`QI.uhlmann_fidelity`) states that `F(ρ, σ)` is the maximum of
`‖tr (Aᴴ * B)‖` over all purifications `A` of `ρ` and `B` of `σ`.  The maximum is attained already
with a purifying system of the same dimension as the original one, and
`QI.overlap_le_fidelity` shows that no larger purifying system can do better.

The main ingredients proved along the way are a polar-type decomposition of matrices
(`QI.exists_unitary_mul_of_mul_conjTranspose_eq` and its rectangular contraction version), the
Hilbert–Schmidt Cauchy–Schwarz inequality (`QI.abs_trace_conjTranspose_mul_le`) and the bound
`‖tr (P * U)‖ ≤ tr P` for `P` positive semidefinite and `U` a contraction
(`QI.abs_trace_mul_contraction_le`).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

/-! ### Norms of matrix-vector products -/

private lemma toEuclideanLin_apply' {p q : Type*} [Fintype q] [DecidableEq q]
    (M : Matrix p q ℂ) (v : EuclideanSpace ℂ q) :
    Matrix.toEuclideanLin M v = WithLp.toLp 2 (M *ᵥ (WithLp.ofLp v)) := rfl

private lemma inner_toEuclideanLin_self {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (M : Matrix p q ℂ) (x : EuclideanSpace ℂ q) :
    (inner ℂ (Matrix.toEuclideanLin M x) (Matrix.toEuclideanLin M x) : ℂ)
      = star (WithLp.ofLp x) ⬝ᵥ ((Mᴴ * M) *ᵥ (WithLp.ofLp x)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [toEuclideanLin_apply', WithLp.ofLp_toLp, Matrix.star_mulVec]
  rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

private lemma dotProduct_conjTranspose_mul_self {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq q] (M : Matrix p q ℂ) (x : EuclideanSpace ℂ q) :
    star (WithLp.ofLp x) ⬝ᵥ ((Mᴴ * M) *ᵥ (WithLp.ofLp x))
      = ((‖(Matrix.toEuclideanLin M x)‖ : ℝ) : ℂ) ^ 2 := by
  rw [← inner_toEuclideanLin_self, inner_self_eq_norm_sq_to_K]
  simp

/-! ### Contractions -/

/-- A matrix `M` is a contraction if `Mᴴ * M ≤ 1`, equivalently if the associated linear map does
not increase the Euclidean norm (see `QI.isContraction_iff`). -/
def IsContraction {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q] (M : Matrix p q ℂ) : Prop :=
  (1 - Mᴴ * M).PosSemidef

theorem isContraction_iff {p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]
    (M : Matrix p q ℂ) :
    IsContraction M ↔ ∀ x : EuclideanSpace ℂ q, ‖Matrix.toEuclideanLin M x‖ ≤ ‖x‖ := by
  have hherm : (1 - Mᴴ * M).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hself : ∀ x : EuclideanSpace ℂ q,
      star (WithLp.ofLp x) ⬝ᵥ ((1 - Mᴴ * M) *ᵥ (WithLp.ofLp x))
        = (((‖x‖ : ℝ) ^ 2 - ‖Matrix.toEuclideanLin M x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      dotProduct_conjTranspose_mul_self M x]
    have h2 : star (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x) = ((‖x‖ : ℝ) : ℂ) ^ 2 := by
      simpa using dotProduct_conjTranspose_mul_self (1 : Matrix q q ℂ) x
    rw [h2]; push_cast; ring
  constructor
  · intro h x
    have h1 := h.dotProduct_mulVec_nonneg (WithLp.ofLp x)
    rw [hself x] at h1
    have h2 : (0 : ℝ) ≤ ‖x‖ ^ 2 - ‖Matrix.toEuclideanLin M x‖ ^ 2 := by exact_mod_cast h1
    nlinarith [norm_nonneg (Matrix.toEuclideanLin M x), norm_nonneg x]
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun x => ?_)
    have hx := hself (WithLp.toLp 2 x)
    rw [hx]
    have h1 := h (WithLp.toLp 2 x)
    have h2 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ q)‖ ^ 2
        - ‖Matrix.toEuclideanLin M (WithLp.toLp 2 x)‖ ^ 2 := by
      nlinarith [norm_nonneg (Matrix.toEuclideanLin M (WithLp.toLp 2 x)),
        norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ q)]
    exact_mod_cast h2

theorem isContraction_of_mem_unitary {q : Type*} [Fintype q] [DecidableEq q]
    {U : Matrix q q ℂ} (hU : U ∈ unitary (Matrix q q ℂ)) : IsContraction U := by
  have h : Uᴴ * U = 1 := by simpa using (Unitary.mem_iff.mp hU).1
  simpa [IsContraction, h] using (Matrix.PosSemidef.zero : (0 : Matrix q q ℂ).PosSemidef)

theorem IsContraction.mul {p q r : Type*} [Fintype p] [Fintype q] [Fintype r] [DecidableEq q]
    [DecidableEq r] {M : Matrix p q ℂ} {N : Matrix q r ℂ} (hM : IsContraction M)
    (hN : IsContraction N) : IsContraction (M * N) := by
  rw [isContraction_iff] at hM hN ⊢
  intro x
  have hcomp : Matrix.toEuclideanLin (M * N) x
      = Matrix.toEuclideanLin M (Matrix.toEuclideanLin N x) := by
    simp [toEuclideanLin_apply', Matrix.mulVec_mulVec]
  rw [hcomp]
  exact (hM _).trans (hN x)

theorem IsContraction.conjTranspose {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] {M : Matrix p q ℂ} (h : IsContraction M) : IsContraction Mᴴ := by
  rw [isContraction_iff] at h ⊢
  intro y
  set z : EuclideanSpace ℂ q := Matrix.toEuclideanLin Mᴴ y with hz
  have key : ((‖z‖ : ℝ) : ℂ) ^ 2 = inner ℂ y (Matrix.toEuclideanLin M z) := by
    rw [hz, ← dotProduct_conjTranspose_mul_self Mᴴ y, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [toEuclideanLin_apply', WithLp.ofLp_toLp, Matrix.conjTranspose_conjTranspose,
      Matrix.mulVec_mulVec]
    rw [dotProduct_comm]
  have h1 : ‖z‖ ^ 2 = ‖(inner ℂ y (Matrix.toEuclideanLin M z) : ℂ)‖ := by rw [← key]; simp
  have h2 : ‖(inner ℂ y (Matrix.toEuclideanLin M z) : ℂ)‖ ≤ ‖y‖ * ‖Matrix.toEuclideanLin M z‖ :=
    norm_inner_le_norm _ _
  have h3 : ‖Matrix.toEuclideanLin M z‖ ≤ ‖z‖ := h z
  nlinarith [norm_nonneg z, norm_nonneg y]

/-! ### Polar-type decompositions

Two matrices with the same "Gram matrix" `A * Aᴴ` differ by a unitary (or, in the rectangular
case, contractive) factor on the right.  This is the algebraic heart of Uhlmann's theorem: two
purifications of the same state are related by a unitary on the purifying system. -/

/-- If two linear maps out of a finite-dimensional inner product space have pointwise equal norms,
then the second factors through the first by a linear isometry defined on the range. -/
private lemma exists_isometry_on_range {n m : Type*} [Fintype n] [Fintype m]
    {f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n}
    {g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m} (hnorm : ∀ x, ‖g x‖ = ‖f x‖) :
    ∃ L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ m,
      ∀ x : EuclideanSpace ℂ n, L ⟨f x, ⟨x, rfl⟩⟩ = g x := by
  classical
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hgx : ‖g x‖ = 0 := by rw [hnorm x, LinearMap.mem_ker.mp hx, norm_zero]
    simpa [LinearMap.mem_ker] using norm_eq_zero.mp hgx
  set L₀ : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ m :=
    (Submodule.liftQ _ g hker) ∘ₗ
      (f.quotKerEquivRange.symm : (LinearMap.range f) →ₗ[ℂ] _) with hL₀def
  have hL₀ : ∀ x : EuclideanSpace ℂ n, L₀ ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    have hsymm : f.quotKerEquivRange.symm ⟨f x, ⟨x, rfl⟩⟩ = Submodule.Quotient.mk x := by
      apply f.quotKerEquivRange.injective
      simp
    simp [hL₀def, hsymm]
  have hnormL₀ : ∀ y : (LinearMap.range f), ‖L₀ y‖ = ‖y‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hL₀ x]
    simpa using hnorm x
  exact ⟨⟨L₀, hnormL₀⟩, hL₀⟩

/-- Two endomorphisms of a finite-dimensional inner product space with pointwise equal norms
differ by a surjective linear isometry. -/
private lemma exists_isometryEquiv_comp {n : Type*} [Fintype n]
    {f g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n} (hnorm : ∀ x, ‖g x‖ = ‖f x‖) :
    ∃ L : EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ n, ∀ x, L (f x) = g x := by
  obtain ⟨L₁, hL₁⟩ := exists_isometry_on_range hnorm
  refine ⟨L₁.extend.toLinearIsometryEquiv rfl, fun x => ?_⟩
  have hext : L₁.extend ((⟨f x, ⟨x, rfl⟩⟩ : LinearMap.range f) : EuclideanSpace ℂ n)
      = L₁ ⟨f x, ⟨x, rfl⟩⟩ := LinearIsometry.extend_apply _ _
  simpa [hL₁ x] using hext

/-- Two linear maps with pointwise equal norms, with possibly different targets, differ by a
linear contraction. -/
private lemma exists_contraction_comp {n m : Type*} [Fintype n] [Fintype m]
    {f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n}
    {g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m} (hnorm : ∀ x, ‖g x‖ = ‖f x‖) :
    ∃ L : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m,
      (∀ x, L (f x) = g x) ∧ ∀ x, ‖L x‖ ≤ ‖x‖ := by
  classical
  obtain ⟨L₁, hL₁⟩ := exists_isometry_on_range hnorm
  refine ⟨L₁.toLinearMap ∘ₗ
    ((LinearMap.range f).orthogonalProjection : _ →L[ℂ] _).toLinearMap, fun x => ?_, fun x => ?_⟩
  · have hproj : (LinearMap.range f).orthogonalProjection (f x)
        = (⟨f x, ⟨x, rfl⟩⟩ : LinearMap.range f) := by
      simpa using Submodule.orthogonalProjection_mem_subspace_eq_self
        (K := LinearMap.range f) ⟨f x, ⟨x, rfl⟩⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometry.coe_toLinearMap, hproj]
    exact hL₁ x
  · have h1 : ‖L₁ ((LinearMap.range f).orthogonalProjection x)‖
        = ‖((LinearMap.range f).orthogonalProjection x : EuclideanSpace ℂ n)‖ :=
      L₁.norm_map _
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometry.coe_toLinearMap, h1]
    exact Submodule.norm_orthogonalProjection_apply_le _ x

/-- Every surjective linear isometry of `EuclideanSpace ℂ n` is given by a unitary matrix. -/
private lemma exists_unitary_matrix_of_isometryEquiv {n : Type*} [Fintype n] [DecidableEq n]
    (L : EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ n) :
    ∃ V : Matrix n n ℂ, V ∈ unitary (Matrix n n ℂ) ∧
      ∀ x : n → ℂ, V *ᵥ x = WithLp.ofLp (L (WithLp.toLp 2 x)) := by
  classical
  set V : Matrix n n ℂ := Matrix.toEuclideanLin.symm (L.toLinearEquiv.toLinearMap) with hVdef
  have hV : ∀ x : EuclideanSpace ℂ n, WithLp.toLp 2 (V *ᵥ (WithLp.ofLp x)) = L x := by
    intro x
    have h1 := Matrix.toEuclideanLin.apply_symm_apply (L.toLinearEquiv.toLinearMap)
    have h2 : (Matrix.toEuclideanLin V) x = L x := by rw [hVdef, h1]; rfl
    rw [toEuclideanLin_apply'] at h2
    exact h2
  have hVunit : Vᴴ * V = 1 := by
    ext i j
    have hinner :
        (inner ℂ (L (EuclideanSpace.single i (1:ℂ))) (L (EuclideanSpace.single j (1:ℂ))) : ℂ)
          = inner ℂ (EuclideanSpace.single i (1:ℂ)) (EuclideanSpace.single j (1:ℂ)) :=
      L.inner_map_map _ _
    rw [← hV, ← hV] at hinner
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simp only [EuclideanSpace.single, WithLp.ofLp_toLp, Matrix.mulVec_single] at hinner
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct,
      Pi.star_apply, RCLike.star_def] at *
    simp only [Matrix.col_apply, MulOpposite.op_one, one_smul, Pi.single_apply] at hinner
    have hswap : ∑ x, (starRingEnd ℂ) (V x i) * V x j = ∑ x, V x j * (starRingEnd ℂ) (V x i) := by
      simp [mul_comm]
    rw [hswap, hinner]
    simp [eq_comm]
  refine ⟨V, ?_, fun x => ?_⟩
  · rw [Unitary.mem_iff]
    exact ⟨hVunit, mul_eq_one_comm.mp hVunit⟩
  · have := hV (WithLp.toLp 2 x)
    simpa using congrArg WithLp.ofLp this

/-- The matrix of a linear contraction is a contraction. -/
private lemma isContraction_toEuclideanLin_symm {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] (L : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m) (hL : ∀ x, ‖L x‖ ≤ ‖x‖) :
    IsContraction (Matrix.toEuclideanLin.symm L) := by
  rw [isContraction_iff]
  intro x
  rw [Matrix.toEuclideanLin.apply_symm_apply]
  exact hL x

private lemma norm_conjTranspose_mulVec_eq {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    (A : Matrix n m ℂ) (R : Matrix n n ℂ) (h : A * Aᴴ = R * Rᴴ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin Aᴴ x‖ = ‖Matrix.toEuclideanLin Rᴴ x‖ := by
  have h1 := dotProduct_conjTranspose_mul_self Aᴴ x
  have h2 := dotProduct_conjTranspose_mul_self Rᴴ x
  rw [Matrix.conjTranspose_conjTranspose, h] at h1
  rw [Matrix.conjTranspose_conjTranspose] at h2
  rw [h2] at h1
  have h3 : ‖Matrix.toEuclideanLin Rᴴ x‖ ^ 2 = ‖Matrix.toEuclideanLin Aᴴ x‖ ^ 2 := by
    exact_mod_cast h1
  nlinarith [norm_nonneg (Matrix.toEuclideanLin Aᴴ x), norm_nonneg (Matrix.toEuclideanLin Rᴴ x)]

/-- **Polar-type decomposition.** If `A * Aᴴ = R * Rᴴ` for square matrices `A` and `R`, then
`A = R * W` for some unitary `W`. -/
theorem exists_unitary_mul_of_mul_conjTranspose_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A R : Matrix n n ℂ} (h : A * Aᴴ = R * Rᴴ) :
    ∃ W : Matrix n n ℂ, W ∈ unitary (Matrix n n ℂ) ∧ A = R * W := by
  classical
  obtain ⟨L, hL⟩ :=
    exists_isometryEquiv_comp (f := Matrix.toEuclideanLin Rᴴ) (g := Matrix.toEuclideanLin Aᴴ)
      (fun x => norm_conjTranspose_mulVec_eq A R h x)
  obtain ⟨V, hVmem, hVapp⟩ := exists_unitary_matrix_of_isometryEquiv L
  have hmul : V * Rᴴ = Aᴴ := by
    ext i j
    have hx := hL (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
    have h1 : V *ᵥ (Rᴴ *ᵥ (Pi.single j (1 : ℂ))) = Aᴴ *ᵥ (Pi.single j (1 : ℂ)) := by
      have hfx : WithLp.ofLp (Matrix.toEuclideanLin Rᴴ (WithLp.toLp 2 (Pi.single j (1 : ℂ))))
          = Rᴴ *ᵥ Pi.single j (1 : ℂ) := by simp [toEuclideanLin_apply']
      have hgx : WithLp.ofLp (Matrix.toEuclideanLin Aᴴ (WithLp.toLp 2 (Pi.single j (1 : ℂ))))
          = Aᴴ *ᵥ Pi.single j (1 : ℂ) := by simp [toEuclideanLin_apply']
      have hcong := congrArg WithLp.ofLp hx
      rw [hgx] at hcong
      rw [← hcong, hVapp]
      congr 1
    rw [Matrix.mulVec_mulVec] at h1
    have := congrFun h1 i
    simpa [Matrix.mulVec_single] using this
  refine ⟨Vᴴ, Unitary.star_mem hVmem, ?_⟩
  have := congrArg Matrix.conjTranspose hmul
  simpa [Matrix.conjTranspose_mul] using this.symm

/-- **Rectangular polar-type decomposition.** If `A * Aᴴ = R * Rᴴ` with `A : Matrix n m ℂ` and
`R : Matrix n n ℂ`, then `A = R * W` for a matrix `W` such that both `W` and `Wᴴ` are
contractions. -/
theorem exists_contraction_mul_of_mul_conjTranspose_eq {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] {A : Matrix n m ℂ} {R : Matrix n n ℂ} (h : A * Aᴴ = R * Rᴴ) :
    ∃ W : Matrix n m ℂ, A = R * W ∧ IsContraction W ∧ IsContraction Wᴴ := by
  classical
  obtain ⟨L, hLcomp, hLcontr⟩ :=
    exists_contraction_comp (f := Matrix.toEuclideanLin Rᴴ) (g := Matrix.toEuclideanLin Aᴴ)
      (fun x => norm_conjTranspose_mulVec_eq A R h x)
  set V : Matrix m n ℂ := Matrix.toEuclideanLin.symm L with hVdef
  have hVcontr : IsContraction V := isContraction_toEuclideanLin_symm L hLcontr
  have hVapp : ∀ x : EuclideanSpace ℂ n, Matrix.toEuclideanLin V x = L x := by
    intro x; rw [hVdef, Matrix.toEuclideanLin.apply_symm_apply]
  have hmul : V * Rᴴ = Aᴴ := by
    ext i j
    have hx := hLcomp (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
    have h1 : V *ᵥ (Rᴴ *ᵥ (Pi.single j (1 : ℂ))) = Aᴴ *ᵥ (Pi.single j (1 : ℂ)) := by
      have hfx : Matrix.toEuclideanLin V (Matrix.toEuclideanLin Rᴴ
            (WithLp.toLp 2 (Pi.single j (1 : ℂ))))
          = Matrix.toEuclideanLin Aᴴ (WithLp.toLp 2 (Pi.single j (1 : ℂ))) := by
        rw [hVapp, hx]
      have := congrArg WithLp.ofLp hfx
      simpa [toEuclideanLin_apply'] using this
    rw [Matrix.mulVec_mulVec] at h1
    have := congrFun h1 i
    simpa [Matrix.mulVec_single] using this
  refine ⟨Vᴴ, ?_, hVcontr.conjTranspose, ?_⟩
  · have := congrArg Matrix.conjTranspose hmul
    simpa [Matrix.conjTranspose_mul] using this.symm
  · simpa using hVcontr

/-! ### The Hilbert–Schmidt Cauchy–Schwarz inequality -/

/-- A matrix, viewed as a vector in the Hilbert space `EuclideanSpace ℂ (n × n)`. -/
private noncomputable def hsVec {n : Type*} [Fintype n] (M : Matrix n n ℂ) :
    EuclideanSpace ℂ (n × n) :=
  WithLp.toLp 2 (fun p : n × n => M p.1 p.2)

private lemma inner_hsVec {n : Type*} [Fintype n] (X Y : Matrix n n ℂ) :
    (inner ℂ (hsVec X) (hsVec Y) : ℂ) = (Xᴴ * Y).trace := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [hsVec, WithLp.ofLp_toLp, dotProduct, Pi.star_apply, RCLike.star_def,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  exact Fintype.sum_equiv (Equiv.prodComm n n) _ _ (fun p => by simp [mul_comm])

/-- Cauchy–Schwarz for the Hilbert–Schmidt (Frobenius) inner product on matrices. -/
theorem abs_trace_conjTranspose_mul_le {n : Type*} [Fintype n] (X Y : Matrix n n ℂ) :
    ‖(Xᴴ * Y).trace‖ ≤ Real.sqrt ((Xᴴ * X).trace.re) * Real.sqrt ((Yᴴ * Y).trace.re) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hsVec X) (hsVec Y)
  rw [inner_hsVec] at h
  have hX : ‖hsVec X‖ = Real.sqrt ((Xᴴ * X).trace.re) := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_hsVec, RCLike.re_to_complex]
  have hY : ‖hsVec Y‖ = Real.sqrt ((Yᴴ * Y).trace.re) := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_hsVec, RCLike.re_to_complex]
  rwa [hX, hY] at h

/-- The trace of a positive semidefinite matrix is a nonnegative real. -/
private lemma trace_re_nonneg {n : Type*} [Fintype n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    0 ≤ P.trace.re :=
  (Complex.le_def.mp hP.trace_nonneg).1

/-- For `P` positive semidefinite and `U` a contraction, `|tr (P U)| ≤ tr P`. -/
theorem abs_trace_mul_contraction_le {n : Type*} [Fintype n] [DecidableEq n] {P U : Matrix n n ℂ}
    (hP : P.PosSemidef) (hU : IsContraction U) : ‖(P * U).trace‖ ≤ P.trace.re := by
  set S : Matrix n n ℂ := CFC.sqrt P with hSdef
  have hS : S.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P (by exact hP.nonneg)
  have hSH : Sᴴ = S := hS.isHermitian
  have htr : (P * U).trace = (Sᴴ * (U * S)).trace := by
    rw [hSH, ← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm S (S * U), Matrix.mul_assoc]
  have h1 : (Sᴴ * S).trace = P.trace := by rw [hSH, hSS]
  have hD : (Sᴴ * (1 - Uᴴ * U) * S).PosSemidef := hU.conjTranspose_mul_mul_same S
  have hDexp : Sᴴ * (1 - Uᴴ * U) * S = Sᴴ * S - (U * S)ᴴ * (U * S) := by
    rw [Matrix.conjTranspose_mul]
    noncomm_ring
  have h2 : ((U * S)ᴴ * (U * S)).trace.re ≤ P.trace.re := by
    have h3 := trace_re_nonneg hD
    rw [hDexp, Matrix.trace_sub, Complex.sub_re, h1] at h3
    linarith
  have hcs := abs_trace_conjTranspose_mul_le S (U * S)
  rw [h1] at hcs
  rw [htr]
  refine hcs.trans ?_
  calc Real.sqrt P.trace.re * Real.sqrt (((U * S)ᴴ * (U * S)).trace.re)
      ≤ Real.sqrt P.trace.re * Real.sqrt P.trace.re :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    _ = P.trace.re := Real.mul_self_sqrt (trace_re_nonneg hP)

/-- For `P` positive semidefinite and `U` unitary, `|tr (P U)| ≤ tr P`. -/
theorem abs_trace_mul_unitary_le {n : Type*} [Fintype n] [DecidableEq n] {P U : Matrix n n ℂ}
    (hP : P.PosSemidef) (hU : U ∈ unitary (Matrix n n ℂ)) : ‖(P * U).trace‖ ≤ P.trace.re :=
  abs_trace_mul_contraction_le hP (isContraction_of_mem_unitary hU)

/-! ### Fidelity and Uhlmann's theorem -/

/-- The fidelity of two positive semidefinite matrices (in particular, of two density matrices),
`F(ρ, σ) = tr √(√ρ σ √ρ)`. -/
noncomputable def fidelity {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace.re

section Uhlmann

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ}

/-- The overlap of any two purifications, on an arbitrary purifying system, of `ρ` and `σ` is at
most the fidelity of `ρ` and `σ`. -/
theorem overlap_le_fidelity {m : Type*} [Fintype m] [DecidableEq m] (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) {A B : Matrix n m ℂ} (hA : A * Aᴴ = ρ) (hB : B * Bᴴ = σ) :
    ‖(Aᴴ * B).trace‖ ≤ fidelity ρ σ := by
  classical
  set P : Matrix n n ℂ := CFC.sqrt ρ with hPdef
  set Q : Matrix n n ℂ := CFC.sqrt σ with hQdef
  have hP : P.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hQ : Q.PosSemidef := (CFC.sqrt_nonneg σ).posSemidef
  have hPP : P * P = ρ := CFC.sqrt_mul_sqrt_self ρ (by exact hρ.nonneg)
  have hQQ : Q * Q = σ := CFC.sqrt_mul_sqrt_self σ (by exact hσ.nonneg)
  have hPH : Pᴴ = P := hP.isHermitian
  have hQH : Qᴴ = Q := hQ.isHermitian
  have hNNH : (P * Q) * (P * Q)ᴴ = P * σ * P := by
    rw [Matrix.conjTranspose_mul, hPH, hQH, Matrix.mul_assoc, ← Matrix.mul_assoc Q Q P,
      hQQ, Matrix.mul_assoc]
  set R : Matrix n n ℂ := CFC.sqrt (P * σ * P) with hRdef
  have hNNHpsd : (P * σ * P).PosSemidef := by
    rw [← hNNH]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hR : R.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hRR : R * R = P * σ * P := CFC.sqrt_mul_sqrt_self _ (by exact hNNHpsd.nonneg)
  have hRH : Rᴴ = R := hR.isHermitian
  obtain ⟨W, hWmem, hW⟩ :=
    exists_unitary_mul_of_mul_conjTranspose_eq (A := P * Q) (R := R) (by rw [hNNH, hRH, hRR])
  obtain ⟨W₁, hW₁, hW₁c, hW₁c'⟩ :=
    exists_contraction_mul_of_mul_conjTranspose_eq (A := A) (R := P) (by rw [hA, hPH, hPP])
  obtain ⟨W₂, hW₂, hW₂c, hW₂c'⟩ :=
    exists_contraction_mul_of_mul_conjTranspose_eq (A := B) (R := Q) (by rw [hB, hQH, hQQ])
  have hU : IsContraction (W * (W₂ * W₁ᴴ)) :=
    (isContraction_of_mem_unitary hWmem).mul (hW₂c.mul hW₁c')
  have hkey : (Aᴴ * B).trace = (R * (W * (W₂ * W₁ᴴ))).trace := by
    rw [hW₁, hW₂, Matrix.conjTranspose_mul, hPH]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P Q W₂, hW]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [hkey]
  exact abs_trace_mul_contraction_le hR hU

/-- **Uhlmann's theorem.**  The fidelity of two states `ρ, σ` of an `n`-dimensional system is the
maximum of the overlaps `|⟨ψ|φ⟩|` over all purifications `ψ` of `ρ` and `φ` of `σ` living in
`ℂ^n ⊗ ℂ^n`.  A vector of `ℂ^n ⊗ ℂ^n` is encoded as a matrix `A : Matrix n n ℂ`; then its
reduced density matrix on the first factor is `A * Aᴴ`, and the overlap of the vectors encoded by
`A` and `B` is `tr (Aᴴ * B)`. -/
theorem uhlmann_fidelity (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ A B : Matrix n n ℂ, A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ x = ‖(Aᴴ * B).trace‖}
      (fidelity ρ σ) := by
  classical
  set P : Matrix n n ℂ := CFC.sqrt ρ with hPdef
  set Q : Matrix n n ℂ := CFC.sqrt σ with hQdef
  have hP : P.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hQ : Q.PosSemidef := (CFC.sqrt_nonneg σ).posSemidef
  have hPP : P * P = ρ := CFC.sqrt_mul_sqrt_self ρ (by exact hρ.nonneg)
  have hQQ : Q * Q = σ := CFC.sqrt_mul_sqrt_self σ (by exact hσ.nonneg)
  have hPH : Pᴴ = P := hP.isHermitian
  have hQH : Qᴴ = Q := hQ.isHermitian
  have hNNH : (P * Q) * (P * Q)ᴴ = P * σ * P := by
    rw [Matrix.conjTranspose_mul, hPH, hQH, Matrix.mul_assoc, ← Matrix.mul_assoc Q Q P,
      hQQ, Matrix.mul_assoc]
  set R : Matrix n n ℂ := CFC.sqrt (P * σ * P) with hRdef
  have hNNHpsd : (P * σ * P).PosSemidef := by
    rw [← hNNH]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hR : R.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hRR : R * R = P * σ * P := CFC.sqrt_mul_sqrt_self _ (by exact hNNHpsd.nonneg)
  have hRH : Rᴴ = R := hR.isHermitian
  have hfid : fidelity ρ σ = R.trace.re := rfl
  obtain ⟨W, hWmem, hW⟩ :=
    exists_unitary_mul_of_mul_conjTranspose_eq (A := P * Q) (R := R) (by rw [hNNH, hRH, hRR])
  obtain ⟨hW1, hW2⟩ := Unitary.mem_iff.mp hWmem
  have hWW : Wᴴ * W = 1 := by simpa using hW1
  have hWW' : W * Wᴴ = 1 := by simpa using hW2
  have htraceR : ‖R.trace‖ = R.trace.re := by
    have h0 : (0 : ℂ) ≤ R.trace := hR.trace_nonneg
    have him : R.trace.im = 0 := ((Complex.le_def.mp h0).2).symm
    rw [Complex.norm_def, Complex.normSq_apply, him]
    simpa using Real.sqrt_mul_self (trace_re_nonneg hR)
  constructor
  · -- the value is attained
    refine ⟨P, Q * Wᴴ, ?_, ?_, ?_⟩
    · rw [hPH, hPP]
    · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc Wᴴ W Qᴴ, hWW, Matrix.one_mul, hQH, hQQ]
    · rw [hPH, ← Matrix.mul_assoc, hW, Matrix.mul_assoc, hWW', Matrix.mul_one, hfid, htraceR]
  · -- the value is an upper bound
    rintro x ⟨A, B, hA, hB, rfl⟩
    exact overlap_le_fidelity hρ hσ hA hB

end Uhlmann

end QI

