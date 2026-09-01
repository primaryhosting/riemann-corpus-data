import Mathlib

set_option maxHeartbeats 1000000

/-!
# Purification of mixed states

A mixed state on a finite dimensional system `n` is a positive semidefinite matrix `rho` of
trace one.  A *purification* of `rho` is a unit vector `psi` on the composite system
`n × m` (system ⊗ ancilla) whose reduced density matrix (partial trace over the ancilla `m`)
is `rho`.

The main theorem `QI.purification_exists` states that

* every mixed state admits a purification (with ancilla a copy of the system), and
* any two purifications of the same mixed state are related by an isometry acting on the
  ancilla alone (in particular, for ancillas of the same dimension, by a unitary).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

section Defs

variable {n m : Type*}

/-- The matrix `A` whose `(i,k)` entry is `psi (i,k)`; this is the standard identification of a
vector of the composite system `n × m` with a linear map. -/
def toMat (psi : n × m → ℂ) : Matrix n m ℂ := Matrix.of fun i k => psi (i, k)

@[simp] lemma toMat_apply (psi : n × m → ℂ) (i : n) (k : m) : toMat psi i k = psi (i, k) := rfl

/-- The density matrix of the pure state `psi`, i.e. `|psi⟩⟨psi|`. -/
def pureProj {N : Type*} (psi : N → ℂ) : Matrix N N ℂ :=
  Matrix.of fun a b => psi a * star (psi b)

/-- The partial trace over the second (ancilla) factor. -/
noncomputable def ptraceAncilla [Fintype m] (M : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k : m, M (i, k) (j, k)

/-- A mixed state (density matrix): positive semidefinite with unit trace. -/
structure IsMixedState [Fintype n] (rho : Matrix n n ℂ) : Prop where
  posSemidef : rho.PosSemidef
  trace_eq_one : rho.trace = 1

/-- `psi`, a vector of the composite system `n × m`, is a purification of `rho` if the partial
trace over the ancilla of `|psi⟩⟨psi|` is `rho`. -/
def IsPurification [Fintype m] (rho : Matrix n n ℂ) (psi : n × m → ℂ) : Prop :=
  ptraceAncilla (pureProj psi) = rho

/-- The action of an operator `V` on the ancilla factor alone, i.e. `(1 ⊗ V) psi`. -/
noncomputable def ancillaAction {m₁ m₂ : Type*} [Fintype m₁] (V : Matrix m₂ m₁ ℂ) (psi : n × m₁ → ℂ) :
    n × m₂ → ℂ :=
  fun p => ∑ l : m₁, V p.2 l * psi (p.1, l)

end Defs

section Basic

variable {n m : Type*} [Fintype m]

lemma ptrace_pureProj (psi : n × m → ℂ) :
    ptraceAncilla (pureProj psi) = toMat psi * (toMat psi)ᴴ := by
  ext i j
  simp [ptraceAncilla, pureProj, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma isPurification_iff (rho : Matrix n n ℂ) (psi : n × m → ℂ) :
    IsPurification rho psi ↔ toMat psi * (toMat psi)ᴴ = rho := by
  rw [IsPurification, ptrace_pureProj]

end Basic

section Crux

/-- Two linear maps into a finite dimensional inner product space with the same Gram data are
related by an isometry of the target. -/
theorem exists_isometry_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (fa fb : E →ₗ[ℂ] F) (hinner : ∀ x y, inner ℂ (fa x) (fa y) = inner ℂ (fb x) (fb y)) :
    ∃ L : F →ₗᵢ[ℂ] F, ∀ x, L (fa x) = fb x := by
  have hkerle : LinearMap.ker fa ≤ LinearMap.ker fb := by
    intro x hx
    simp only [LinearMap.mem_ker] at *
    have h2 := hinner x x
    rw [hx] at h2
    simp only [inner_zero_left] at h2
    exact inner_self_eq_zero.mp h2.symm
  set g : (E ⧸ LinearMap.ker fa) →ₗ[ℂ] F := (LinearMap.ker fa).liftQ fb hkerle with hg
  set g0 : (LinearMap.range fa) →ₗ[ℂ] F :=
    g ∘ₗ (fa.quotKerEquivRange.symm : (LinearMap.range fa) →ₗ[ℂ] _) with hg0
  have hg0_apply : ∀ (x : E) (hx : fa x ∈ LinearMap.range fa), g0 ⟨fa x, hx⟩ = fb x := by
    intro x hx
    rw [hg0]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image, hg]
    simp [Submodule.liftQ_apply]
  have hg0iso : ∀ v w : LinearMap.range fa,
      inner ℂ (g0 v) (g0 w) = inner ℂ (v : F) (w : F) := by
    rintro ⟨v, x, rfl⟩ ⟨w, y, rfl⟩
    rw [hg0_apply x, hg0_apply y]
    exact (hinner x y).symm
  refine ⟨(LinearMap.isometryOfInner g0 hg0iso).extend, fun x => ?_⟩
  have h1 :=
    (LinearMap.isometryOfInner g0 hg0iso).extend_apply (⟨fa x, ⟨x, rfl⟩⟩ : LinearMap.range fa)
  simpa [hg0_apply x] using h1

/-- If `A Aᴴ = B Bᴴ` then `B = A U` for some unitary `U`. -/
theorem exists_unitary_of_mul_conjTranspose_eq {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (A B : Matrix n m ℂ) (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix m m ℂ, Uᴴ * U = 1 ∧ B = A * U := by
  have hmulLin : ∀ (C : Matrix n m ℂ) (x y : EuclideanSpace ℂ n),
      inner ℂ ((Matrix.toEuclideanLin Cᴴ) x) ((Matrix.toEuclideanLin Cᴴ) y)
        = inner ℂ x ((Matrix.toEuclideanLin (C * Cᴴ)) y) := by
    intro C x y
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
    congr 1
    rw [toLpLin_mul 2 2 2 C Cᴴ]
    simp [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hinner : ∀ x y, inner ℂ ((Matrix.toEuclideanLin Aᴴ) x) ((Matrix.toEuclideanLin Aᴴ) y)
      = inner ℂ ((Matrix.toEuclideanLin Bᴴ) x) ((Matrix.toEuclideanLin Bᴴ) y) := by
    intro x y
    rw [hmulLin A x y, hmulLin B x y, h]
  obtain ⟨L, hL⟩ := exists_isometry_comp _ _ hinner
  set U' : Matrix m m ℂ := Matrix.toEuclideanLin.symm L.toLinearMap with hU'
  have hU'lin : Matrix.toEuclideanLin U' = L.toLinearMap := by rw [hU']; simp
  have hmul : U' * Aᴴ = Bᴴ := by
    apply Matrix.toEuclideanLin.injective
    rw [toLpLin_mul 2 2 2 U' Aᴴ, hU'lin]
    refine LinearMap.ext fun x => ?_
    simpa using hL x
  have hiso : U'ᴴ * U' = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [toLpLin_mul 2 2 2 U'ᴴ U', Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hU'lin]
    refine LinearMap.ext fun x => ?_
    have hkey : ∀ y : EuclideanSpace ℂ m,
        inner ℂ y ((LinearMap.adjoint L.toLinearMap) (L.toLinearMap x)) = inner ℂ y x := by
      intro y
      rw [LinearMap.adjoint_inner_right]
      exact L.inner_map_map y x
    have hx : (LinearMap.adjoint L.toLinearMap) (L.toLinearMap x) = x := ext_inner_left ℂ hkey
    simp only [LinearMap.coe_comp, Function.comp_apply, hx]
    simp
  refine ⟨U'ᴴ, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hiso
  · have h2 := congrArg Matrix.conjTranspose hmul
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose] at h2
    exact h2.symm

/-- The general version: if `A Aᴴ = B Bᴴ` with `B` having a larger "ancilla" index type, then
`B = A * Wᴴ` for an isometry `W`. -/
theorem exists_isometry_of_mul_conjTranspose_eq {n m₁ m₂ : Type*} [Fintype n] [DecidableEq n]
    [Fintype m₁] [DecidableEq m₁] [Fintype m₂] [DecidableEq m₂]
    (A : Matrix n m₁ ℂ) (B : Matrix n m₂ ℂ) (h : A * Aᴴ = B * Bᴴ)
    (hcard : Fintype.card m₁ ≤ Fintype.card m₂) :
    ∃ W : Matrix m₂ m₁ ℂ, Wᴴ * W = 1 ∧ B = A * Wᴴ := by
  obtain ⟨j⟩ : Nonempty (m₁ ↪ m₂) := Function.Embedding.nonempty_of_card_le hcard
  set J : Matrix m₂ m₁ ℂ := Matrix.of (fun k l => if k = j l then 1 else 0) with hJ
  have hJiso : Jᴴ * J = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hJ, Matrix.of_apply,
      Matrix.one_apply]
    rw [Finset.sum_eq_single (j l)]
    · by_cases hll' : l = l'
      · subst hll'; simp
      · simp [hll']
    · intro k _ hk
      simp [hk]
    · simp
  obtain ⟨U, hU, hBU⟩ := exists_unitary_of_mul_conjTranspose_eq (A * Jᴴ) B (by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← h,
      Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J Aᴴ, hJiso, Matrix.one_mul])
  refine ⟨Uᴴ * J, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U Uᴴ J, mul_eq_one_comm.mp hU, Matrix.one_mul, hJiso]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hBU]

/-- Every positive semidefinite matrix of trace one is of the form `A Aᴴ` for a matrix `A` whose
entries have squared norms summing to one. -/
theorem exists_factor_of_isMixedState {n : Type*} [Fintype n] [DecidableEq n]
    {rho : Matrix n n ℂ} (h : IsMixedState rho) :
    ∃ A : Matrix n n ℂ, A * Aᴴ = rho ∧ ∑ a : n × n, ‖A a.1 a.2‖ ^ 2 = 1 := by
  obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hb
  have hA : bᴴ * (bᴴ)ᴴ = rho := by rw [Matrix.conjTranspose_conjTranspose, ← hb]
  refine ⟨bᴴ, hA, ?_⟩
  have key : ((∑ a : n × n, ‖bᴴ a.1 a.2‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h.trace_eq_one, ← hA]
    push_cast
    rw [Matrix.trace, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.mul_conj' _).symm
  exact_mod_cast key

end Crux

section Main

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Purification.** Every mixed state `rho` has a purification (with ancilla a copy of the
system), and any two purifications of `rho` are related by an isometry acting on the ancilla
alone; when the two ancillas have the same dimension this isometry is a unitary. -/
theorem purification_exists {rho : Matrix n n ℂ} (h : IsMixedState rho) :
    (∃ psi : n × n → ℂ, IsPurification rho psi ∧ ∑ a : n × n, ‖psi a‖ ^ 2 = 1) ∧
      (∀ (m₁ m₂ : Type) [Fintype m₁] [DecidableEq m₁] [Fintype m₂] [DecidableEq m₂]
        (psi₁ : n × m₁ → ℂ) (psi₂ : n × m₂ → ℂ), IsPurification rho psi₁ →
        IsPurification rho psi₂ → Fintype.card m₁ ≤ Fintype.card m₂ →
        ∃ V : Matrix m₂ m₁ ℂ, Vᴴ * V = 1 ∧ psi₂ = ancillaAction V psi₁) := by
  constructor
  · obtain ⟨A, hA, hnorm⟩ := exists_factor_of_isMixedState h
    refine ⟨fun p => A p.1 p.2, ?_, hnorm⟩
    rw [isPurification_iff]
    exact hA
  · intro m₁ m₂ _ _ _ _ psi₁ psi₂ h₁ h₂ hcard
    rw [isPurification_iff] at h₁ h₂
    obtain ⟨W, hW, hBW⟩ :=
      exists_isometry_of_mul_conjTranspose_eq (toMat psi₁) (toMat psi₂) (by rw [h₁, h₂]) hcard
    refine ⟨W.map star, ?_, ?_⟩
    · have key : (W.map star)ᴴ * (W.map star) = (Wᴴ * W)ᵀ := by
        ext b b'
        simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, mul_comm]
      rw [key, hW, Matrix.transpose_one]
    · funext p
      have hp := congrFun (congrFun hBW p.1) p.2
      simpa [ancillaAction, Matrix.mul_apply, Matrix.map_apply, mul_comm] using hp

end Main

section Sanity

/-- The maximally mixed state of a qubit is indeed a mixed state. -/
example : IsMixedState (Matrix.diagonal (fun _ : Fin 2 => (1 / 2 : ℂ))) := by
  constructor
  · exact Matrix.posSemidef_diagonal_iff.mpr (fun i => by norm_num [Complex.le_def])
  · simp [Matrix.trace_diagonal]

/-- The Bell state is a purification of the maximally mixed state of a qubit. -/
example : IsPurification (Matrix.diagonal (fun _ : Fin 2 => (1 / 2 : ℂ)))
    (fun p : Fin 2 × Fin 2 => if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0) := by
  rw [isPurification_iff]
  ext i j
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;>
    simp [toMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ext_iff] <;>
    field_simp <;> nlinarith [h2, Real.sqrt_nonneg 2]

end Sanity

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

