import Mathlib

/-!
# Purification of mixed states

A *mixed state* on a finite-dimensional system with index type `n` is a positive semidefinite
matrix `rho : Matrix n n ℂ` of trace `1`.  A *purification* of `rho` with ancilla index type `m`
is a vector `v : n × m → ℂ` in the tensor product whose density matrix `|v⟩⟨v|` has partial
trace over the ancilla equal to `rho`.

The main result `QI.purification_exists` states that every mixed state admits a purification
(with ancilla of the same dimension), and that any two purifications with the same ancilla
differ by a unitary acting on the ancilla alone.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

set_option synthInstance.maxHeartbeats 1000000

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The density matrix `|v⟩⟨v|` of the vector `v`. -/
def outer (v : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec v (star v)

/-- The partial trace over the second tensor factor. -/
noncomputable def ptraceSnd (M : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k, M (i, k) (j, k)

/-- A mixed state is a positive semidefinite matrix of unit trace. -/
structure IsMixedState (rho : Matrix n n ℂ) : Prop where
  posSemidef : rho.PosSemidef
  trace_one : rho.trace = 1

/-- `v : n × m → ℂ` is a purification of the state `rho` if tracing out the ancilla `m`
from the pure state `|v⟩⟨v|` gives back `rho`. -/
def IsPurification (rho : Matrix n n ℂ) (v : n × m → ℂ) : Prop :=
  ptraceSnd (outer v) = rho

/-- A vector in the tensor product, viewed as a matrix. -/
def reshape (v : n × m → ℂ) : Matrix n m ℂ := Matrix.of fun i k => v (i, k)

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
lemma ptraceSnd_outer (v : n × m → ℂ) :
    ptraceSnd (outer v) = reshape v * (reshape v)ᴴ := by
  ext i j
  simp [ptraceSnd, outer, reshape, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply]

omit [DecidableEq n] [DecidableEq m] in
/-- A purification of a state (which has unit trace) is a unit vector. -/
theorem sum_norm_sq_of_isPurification {rho : Matrix n n ℂ} {v : n × m → ℂ}
    (hv : IsPurification rho v) (h1 : rho.trace = 1) :
    ∑ x : n × m, ‖v x‖ ^ 2 = 1 := by
  have hz : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq z
  have h2 : ((∑ x : n × m, ‖v x‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h1, ← hv]
    simp [Matrix.trace, Matrix.diag, ptraceSnd, outer, Matrix.vecMulVec_apply,
      Fintype.sum_prod_type, hz]
  exact_mod_cast h2

/-! ### Linear algebra input: unitary freedom -/

private lemma ofLp_toEuclideanLin {p q : Type*} [Fintype q] [DecidableEq q]
    (M : Matrix p q ℂ) (v : EuclideanSpace ℂ q) :
    (Matrix.toEuclideanLin M v).ofLp = M *ᵥ v.ofLp := rfl

private lemma dotProduct_conj_mulVec {p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix p q ℂ) (x y : q → ℂ) :
    star (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ ((Aᴴ * A) *ᵥ y) := by
  rw [star_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul]

private lemma mem_unitaryGroup_of_dotProduct (W : Matrix m m ℂ)
    (h : ∀ x y : m → ℂ, star (W *ᵥ x) ⬝ᵥ (W *ᵥ y) = star x ⬝ᵥ y) :
    W ∈ Matrix.unitaryGroup m ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  have h1 := h (Pi.single j 1) (Pi.single k 1)
  rw [dotProduct_conj_mulVec] at h1
  have hs : star (Pi.single j (1 : ℂ) : m → ℂ) = Pi.single j 1 := by
    ext i; simp [Pi.single_apply, apply_ite]
  rw [hs, single_one_dotProduct, single_one_dotProduct, Matrix.mulVec_single_one] at h1
  simpa [Matrix.star_eq_conjTranspose, Matrix.one_apply, Pi.single_apply, eq_comm] using h1

private lemma matrix_ext_of_mulVec {p q : Type*} [Fintype q] [DecidableEq q]
    {M N : Matrix p q ℂ} (h : ∀ x : q → ℂ, M *ᵥ x = N *ᵥ x) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

/-- **Unitary freedom**: two matrices with the same Gram matrix differ by a unitary. -/
theorem exists_unitary_mul_eq_of_conjTranspose_mul_eq {A B : Matrix m n ℂ}
    (h : Aᴴ * A = Bᴴ * B) : ∃ W ∈ Matrix.unitaryGroup m ℂ, W * A = B := by
  classical
  set f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m := Matrix.toEuclideanLin A with hfdef
  set g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m := Matrix.toEuclideanLin B with hgdef
  have hinner : ∀ x y : EuclideanSpace ℂ n, ⟪f x, f y⟫_ℂ = ⟪g x, g y⟫_ℂ := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm, dotProduct_comm ((g y).ofLp)]
    simp only [hfdef, hgdef, ofLp_toEuclideanLin]
    rw [dotProduct_conj_mulVec, dotProduct_conj_mulVec, h]
  have hnorm : ∀ x : EuclideanSpace ℂ n, ‖g x‖ = ‖f x‖ := by
    intro x
    have h1 := hinner x x
    have h3 : ‖f x‖ ^ 2 = ‖g x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h1]
    rw [← Real.sqrt_sq (norm_nonneg (g x)), ← h3, Real.sqrt_sq (norm_nonneg (f x))]
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have hx' := hnorm x
    rw [hx, norm_zero] at hx'
    exact norm_eq_zero.mp hx'
  set L0 : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ m :=
    ((LinearMap.ker f).liftQ g hker).comp
      (LinearMap.quotKerEquivRange f).symm.toLinearMap with hL0def
  have hL0 : ∀ x : EuclideanSpace ℂ n,
      L0 ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    have he : (LinearMap.quotKerEquivRange f).symm ⟨f x, LinearMap.mem_range_self f x⟩
        = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f x).symm
    simp [hL0def, he]
  have hL0norm : ∀ s : LinearMap.range f, ‖L0 s‖ = ‖(s : EuclideanSpace ℂ m)‖ := by
    rintro ⟨s, x, rfl⟩
    rw [hL0 x]
    exact hnorm x
  set L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ m := ⟨L0, hL0norm⟩ with hLdef
  set Lext : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m := L.extend with hLextdef
  set W : Matrix m m ℂ := Matrix.toEuclideanLin.symm Lext.toLinearMap with hWdef
  have hWapply : ∀ v : EuclideanSpace ℂ m, W *ᵥ v.ofLp = (Lext v).ofLp := by
    intro v
    rw [← ofLp_toEuclideanLin]
    congr 1
    rw [hWdef, LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨W, ?_, ?_⟩
  · refine mem_unitaryGroup_of_dotProduct W ?_
    intro x y
    have hx := hWapply (WithLp.toLp 2 x)
    have hy := hWapply (WithLp.toLp 2 y)
    have hinn : ⟪Lext (WithLp.toLp 2 x), Lext (WithLp.toLp 2 y)⟫_ℂ
        = ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ m), WithLp.toLp 2 y⟫_ℂ :=
      Lext.inner_map_map _ _
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at hinn
    rw [hx, hy, dotProduct_comm, hinn]
    exact dotProduct_comm _ _
  · refine matrix_ext_of_mulVec ?_
    intro x
    have hfx : f (WithLp.toLp 2 x) = WithLp.toLp 2 (A *ᵥ x) :=
      Matrix.toLpLin_toLp 2 2 A x
    have hgx : g (WithLp.toLp 2 x) = WithLp.toLp 2 (B *ᵥ x) :=
      Matrix.toLpLin_toLp 2 2 B x
    have hext : Lext (f (WithLp.toLp 2 x)) = g (WithLp.toLp 2 x) := by
      have h2 : Lext ((⟨f (WithLp.toLp 2 x), LinearMap.mem_range_self f _⟩ :
          LinearMap.range f) : EuclideanSpace ℂ m)
          = L ⟨f (WithLp.toLp 2 x), LinearMap.mem_range_self f _⟩ :=
        LinearIsometry.extend_apply L _
      simpa [hLdef, hL0] using h2
    rw [← Matrix.mulVec_mulVec]
    have hWA : W *ᵥ (A *ᵥ x) = (Lext (WithLp.toLp 2 (A *ᵥ x))).ofLp := by
      simpa using hWapply (WithLp.toLp 2 (A *ᵥ x))
    rw [hWA, ← hfx, hext, hgx]

/-- Unitary freedom for purifications, in the form `ψ ψᴴ = φ φᴴ`. -/
theorem exists_unitary_mul_eq_of_mul_conjTranspose_eq {psi phi : Matrix n m ℂ}
    (h : psi * psiᴴ = phi * phiᴴ) : ∃ U ∈ Matrix.unitaryGroup m ℂ, psi * U = phi := by
  obtain ⟨W, hW, hWA⟩ := exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (A := psiᴴ) (B := phiᴴ) (by simpa using h)
  refine ⟨Wᴴ, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hW
  · have := congrArg Matrix.conjTranspose hWA
    simpa [Matrix.conjTranspose_mul] using this

/-! ### Main theorem -/

/-- **Purification.**  Every mixed state `rho` has a purification with ancilla of the same
dimension, and any two purifications (with the same ancilla) are related by a unitary acting
on the ancilla only. -/
theorem purification_exists {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Matrix n n ℂ) (hrho : IsMixedState rho) :
    (∃ v : n × n → ℂ, IsPurification rho v) ∧
      ∀ v w : n × n → ℂ, IsPurification rho v → IsPurification rho w →
        ∃ U ∈ Matrix.unitaryGroup n ℂ, ∀ i k, w (i, k) = ∑ l, U k l * v (i, l) := by
  constructor
  · refine ⟨fun p => CFC.sqrt rho p.1 p.2, ?_⟩
    have hsqrt : (CFC.sqrt rho).PosSemidef := (CFC.sqrt_nonneg rho).posSemidef
    show ptraceSnd (outer _) = rho
    rw [ptraceSnd_outer]
    have hre : reshape (fun p : n × n => CFC.sqrt rho p.1 p.2) = CFC.sqrt rho := rfl
    rw [hre, hsqrt.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self rho (ha := hrho.posSemidef.nonneg)
  · intro v w hv hw
    have h : reshape v * (reshape v)ᴴ = reshape w * (reshape w)ᴴ := by
      rw [← ptraceSnd_outer, ← ptraceSnd_outer, hv, hw]
    obtain ⟨U, hU, hUeq⟩ := exists_unitary_mul_eq_of_mul_conjTranspose_eq h
    refine ⟨Uᵀ, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hU
      rw [Matrix.mem_unitaryGroup_iff']
      have hst : star (Uᵀ) = (star U)ᵀ := by
        ext i j; simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
      rw [hst, ← Matrix.transpose_mul, hU, Matrix.transpose_one]
    · intro i k
      have := congrFun (congrFun hUeq i) k
      simpa [reshape, Matrix.mul_apply, mul_comm] using this.symm

/-- **Uniqueness up to an isometry on the ancilla**, for purifications with ancillas of
different dimensions:  if `v` (ancilla `m`) and `w` (ancilla `m'`) both purify `rho`, and the
ancilla of `w` is at least as large, then `w = (1 ⊗ S) v` for an isometry `S` (i.e. `Sᴴ S = 1`)
acting on the ancilla alone. -/
theorem purification_unique_up_to_isometry {n m m' : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (hcard : Fintype.card m ≤ Fintype.card m')
    (rho : Matrix n n ℂ) (v : n × m → ℂ) (w : n × m' → ℂ)
    (hv : IsPurification rho v) (hw : IsPurification rho w) :
    ∃ S : Matrix m' m ℂ, Sᴴ * S = 1 ∧ ∀ i k, w (i, k) = ∑ l, S k l * v (i, l) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  set P : Matrix m m' ℂ := (1 : Matrix m' m' ℂ).submatrix e id with hPdef
  have hPP : P * Pᴴ = 1 := by
    ext i j
    by_cases hij : i = j <;>
      simp [hPdef, Matrix.mul_apply, Matrix.one_apply,
        e.injective.eq_iff, hij, eq_comm, Finset.sum_ite_eq']
  have hgram : (reshape v * P) * (reshape v * P)ᴴ = reshape w * (reshape w)ᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (reshape v), hPP,
      Matrix.mul_one, ← ptraceSnd_outer, ← ptraceSnd_outer, hv, hw]
  obtain ⟨U, hU, hUeq⟩ := exists_unitary_mul_eq_of_mul_conjTranspose_eq hgram
  refine ⟨(P * U)ᵀ, ?_, ?_⟩
  · have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have h1 : (P * U) * (P * U)ᴴ = 1 := by
      rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc P, hUU,
        Matrix.mul_one, hPP]
    have h3 : ((P * U)ᵀ)ᴴ = ((P * U)ᴴ)ᵀ := rfl
    rw [h3, ← Matrix.transpose_mul, h1, Matrix.transpose_one]
  · intro i k
    have := congrFun (congrFun hUeq i) k
    rw [Matrix.mul_assoc] at this
    simpa [reshape, Matrix.mul_apply, mul_comm] using this.symm

/-! ### Sanity check -/

/-- The Bell state `(|00⟩ + |11⟩)/√2` is a purification of the maximally mixed qubit state. -/
theorem ptraceSnd_bell :
    ptraceSnd (outer (fun p : Fin 2 × Fin 2 =>
        if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0))
      = fun i j => if i = j then (1 / 2 : ℂ) else 0 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have key : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv, h2]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptraceSnd, outer, Matrix.vecMulVec_apply] <;> simpa using key

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

