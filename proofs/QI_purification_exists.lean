/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

open scoped MatrixOrder ComplexOrder Kronecker InnerProductSpace
open Matrix

namespace QI

variable {n m : ℕ}

/-- The coefficient matrix of a vector `psi` of the tensor product `ℂ^n ⊗ ℂ^m`, whose
coordinates are indexed by `Fin n × Fin m`. -/
def coeffMatrix (psi : Fin n × Fin m → ℂ) : Matrix (Fin n) (Fin m) ℂ :=
  Matrix.of fun i k => psi (i, k)

/-- The partial trace over the ancilla factor `ℂ^m` of the pure state `|psi⟩⟨psi|`, where
`psi` is a vector of `ℂ^n ⊗ ℂ^m`.  This is the *reduced state* of `psi` on the first
factor. -/
noncomputable def ptrace (psi : Fin n × Fin m → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ∑ k, psi (i, k) * (starRingEnd ℂ) (psi (j, k))

lemma ptrace_eq_mul_conjTranspose (psi : Fin n × Fin m → ℂ) :
    ptrace psi = coeffMatrix psi * (coeffMatrix psi)ᴴ := by
  ext i j
  simp [ptrace, coeffMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- If two `n × m` matrices have the same Gram matrix `A * Aᴴ`, then they differ by a
unitary matrix acting on the right. -/
theorem exists_unitary_of_mul_conjTranspose_eq (A B : Matrix (Fin n) (Fin m) ℂ)
    (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix (Fin m) (Fin m) ℂ, U ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ B = A * U := by
  classical
  set f : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin Aᴴ with hf
  set g : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin Bᴴ with hg
  -- The Gram matrix computes the inner products of the images.
  have hgram : ∀ (C : Matrix (Fin n) (Fin m) ℂ) (x y : EuclideanSpace ℂ (Fin n)),
      ⟪Matrix.toEuclideanLin Cᴴ x, Matrix.toEuclideanLin Cᴴ y⟫_ℂ
        = ⟪x, Matrix.toEuclideanLin (C * Cᴴ) y⟫_ℂ := by
    intro C x y
    rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_left]
    rfl
  have hnorm : ∀ x, ‖f x‖ = ‖g x‖ := by
    intro x
    have hx : ⟪f x, f x⟫_ℂ = ⟪g x, g x⟫_ℂ := by rw [hf, hg, hgram, hgram, h]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hx]
  -- Hence `f x ↦ g x` is a well-defined isometry from the range of `f`.
  have hkerle : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hfx : f x = 0 := hx
    have hgx : ‖g x‖ = 0 := by rw [← hnorm, hfx, norm_zero]
    simpa [LinearMap.mem_ker] using norm_eq_zero.mp hgx
  set L0 : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    ((LinearMap.ker f).liftQ g hkerle) ∘ₗ
      (f.quotKerEquivRange.symm : LinearMap.range f →ₗ[ℂ] _) with hL0def
  have hL0 : ∀ x, L0 ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    rw [hL0def]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
      Submodule.liftQ_apply]
  have hL0norm : ∀ y : LinearMap.range f, ‖L0 y‖ = ‖y‖ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    rw [hL0, ← hnorm]
    rfl
  set L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
    { toLinearMap := L0, norm_map' := hL0norm } with hLdef
  -- Extend it to an isometry of the whole ancilla space.
  set W := L.extend with hWdef
  have hW : ∀ x, W (f x) = g x := by
    intro x
    have hx := L.extend_apply ⟨f x, LinearMap.mem_range_self f x⟩
    rw [hWdef]
    rw [show ((⟨f x, LinearMap.mem_range_self f x⟩ : LinearMap.range f) :
      EuclideanSpace ℂ (Fin m)) = f x from rfl] at hx
    rw [hx, hLdef]
    exact hL0 x
  -- The matrix of that isometry is unitary and conjugates `Aᴴ` into `Bᴴ`.
  set U0 : Matrix (Fin m) (Fin m) ℂ := Matrix.toEuclideanLin.symm W.toLinearMap with hU0def
  have hU0 : Matrix.toEuclideanLin U0 = W.toLinearMap := by
    rw [hU0def, LinearEquiv.apply_symm_apply]
  have hU0mem : U0 ∈ Matrix.unitaryGroup (Fin m) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_one]
    have hstar : (star U0 : Matrix (Fin m) (Fin m) ℂ) = U0ᴴ := rfl
    rw [hstar, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hU0]
    refine LinearMap.ext fun x => ?_
    apply ext_inner_left ℂ
    intro y
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, LinearMap.id_apply]
    exact W.inner_map_map y x
  have hmat : U0 * Aᴴ = Bᴴ := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hU0]
    exact LinearMap.ext fun x => hW x
  refine ⟨U0ᴴ, Unitary.star_mem hU0mem, ?_⟩
  have hcT := congrArg Matrix.conjTranspose hmat
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at hcT
  exact hcT.symm

/-- **Purification.**  Every mixed state `rho` on `ℂ^n` (a positive semidefinite matrix of
trace one) admits a purification: a unit vector `psi` of `ℂ^n ⊗ ℂ^n` whose reduced state on
the first factor is `rho`.  Moreover a purification is unique up to a unitary acting on the
ancilla: any two vectors of `ℂ^n ⊗ ℂ^m` whose reduced state is `rho` are related by
`1 ⊗ U` for some unitary `U` of the ancilla `ℂ^m`. -/
theorem purification_exists (rho : Matrix (Fin n) (Fin n) ℂ)
    (hpos : rho.PosSemidef) (htr : rho.trace = 1) :
    (∃ psi : Fin n × Fin n → ℂ, ptrace psi = rho ∧ ∑ p, ‖psi p‖ ^ 2 = 1) ∧
      (∀ (m : ℕ) (psi phi : Fin n × Fin m → ℂ), ptrace psi = rho → ptrace phi = rho →
        ∃ U : Matrix (Fin m) (Fin m) ℂ, U ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
          phi = ((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ U) *ᵥ psi) := by
  classical
  constructor
  · -- Existence: take the square root of `rho`.
    set S : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt rho with hS
    have hSpos : S.PosSemidef := (CFC.sqrt_nonneg rho).posSemidef
    have hSS : S * S = rho := CFC.sqrt_mul_sqrt_self rho hpos.nonneg
    refine ⟨fun p => S p.1 p.2, ?_, ?_⟩
    · have hc : coeffMatrix (fun p : Fin n × Fin n => S p.1 p.2) = S := rfl
      rw [ptrace_eq_mul_conjTranspose, hc, hSpos.isHermitian.eq, hSS]
    · have h1 : ((∑ p : Fin n × Fin n, ‖S p.1 p.2‖ ^ 2 : ℝ) : ℂ) = 1 := by
        push_cast
        rw [← htr, ← hSS, Matrix.trace]
        simp only [Matrix.diag_apply, Matrix.mul_apply]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [← Complex.mul_conj' (S i k)]
        congr 1
        exact hSpos.isHermitian.apply k i
      exact_mod_cast h1
  · -- Uniqueness up to a unitary on the ancilla.
    intro m psi phi hpsi hphi
    have hgram : coeffMatrix psi * (coeffMatrix psi)ᴴ
        = coeffMatrix phi * (coeffMatrix phi)ᴴ := by
      rw [← ptrace_eq_mul_conjTranspose, ← ptrace_eq_mul_conjTranspose, hpsi, hphi]
    obtain ⟨V, hV, hN⟩ :=
      exists_unitary_of_mul_conjTranspose_eq (coeffMatrix psi) (coeffMatrix phi) hgram
    refine ⟨Vᵀ, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff']
      have h1 : (star (Vᵀ) : Matrix (Fin m) (Fin m) ℂ) * Vᵀ = ((V * star V)ᵀ) := by
        ext a b
        simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_apply, mul_comm]
      rw [h1, Matrix.mem_unitaryGroup_iff.mp hV, Matrix.transpose_one]
    · funext p
      obtain ⟨i, k⟩ := p
      rw [Matrix.mulVec]
      simp only [dotProduct, Matrix.kroneckerMap_apply]
      rw [Fintype.sum_prod_type]
      have hrow : ∀ j : Fin n,
          ∑ l : Fin m, (1 : Matrix (Fin n) (Fin n) ℂ) i j * Vᵀ k l * psi (j, l)
            = (1 : Matrix (Fin n) (Fin n) ℂ) i j * ∑ l : Fin m, V l k * psi (j, l) := by
        intro j
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by simp [Matrix.transpose_apply]; ring
      rw [Finset.sum_congr rfl fun j _ => hrow j, Finset.sum_eq_single i]
      · have hcol : ∑ l : Fin m, V l k * psi (i, l) = (coeffMatrix psi * V) i k := by
          simp only [Matrix.mul_apply, coeffMatrix, Matrix.of_apply]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [Matrix.one_apply_eq, one_mul, hcol, ← hN]
        rfl
      · intro j _ hj
        rw [Matrix.one_apply_ne (Ne.symm hj), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi

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

