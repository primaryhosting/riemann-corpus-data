import Mathlib

/-!
# Rotations of `ℝ³` and a free group of rotations

This file constructs two explicit rotations of `ℝ³` (rotations by the angle `arccos (3/5)`
about the `z`- and `x`-axes) and proves that they generate a free group of rank two.
-/

open Matrix WithLp

namespace BanachTarski

/-- Euclidean three-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-! ### From orthogonal matrices to linear isometries -/

/-- The linear equivalence of `ℝ³` given by an orthogonal matrix. -/
def rotEquiv (M : Matrix (Fin 3) (Fin 3) ℝ) (h : Mᵀ * M = 1) : E ≃ₗ[ℝ] E where
  toFun := fun x => toLp 2 (M *ᵥ ofLp x)
  map_add' := by intro x y; ext i; simp [Matrix.mulVec_add]
  map_smul' := by intro c x; ext i; simp [Matrix.mulVec_smul]
  invFun := fun y => toLp 2 (Mᵀ *ᵥ ofLp y)
  left_inv := by intro x; ext i; simp [Matrix.mulVec_mulVec, h]
  right_inv := by
    intro y; ext i
    show (M *ᵥ ofLp (toLp 2 (Mᵀ *ᵥ ofLp y))) i = ofLp y i
    rw [WithLp.ofLp_toLp, Matrix.mulVec_mulVec, mul_eq_one_comm.mp h, Matrix.one_mulVec]

@[simp] lemma rotEquiv_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (h : Mᵀ * M = 1) (x : E) :
    rotEquiv M h x = toLp 2 (M *ᵥ ofLp x) := rfl

/-- The linear isometry of `ℝ³` given by an orthogonal matrix. -/
noncomputable def rotOf (M : Matrix (Fin 3) (Fin 3) ℝ) (h : Mᵀ * M = 1) : E ≃ₗᵢ[ℝ] E :=
  LinearEquiv.isometryOfInner (rotEquiv M h) (by
    intro x y
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, rotEquiv_apply,
      WithLp.ofLp_toLp]
    show (M *ᵥ ofLp y) ⬝ᵥ (M *ᵥ ofLp x) = (ofLp y) ⬝ᵥ (ofLp x)
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h,
      Matrix.one_mulVec])

@[simp] lemma rotOf_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (h : Mᵀ * M = 1) (x : E) :
    rotOf M h x = toLp 2 (M *ᵥ ofLp x) := rfl

@[simp] lemma rotOf_symm_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (h : Mᵀ * M = 1) (x : E) :
    (rotOf M h).symm x = toLp 2 (Mᵀ *ᵥ ofLp x) := rfl

/-! ### The two generating rotations -/

/-- Rotation by `arccos (3/5)` about the `z`-axis. -/
def Ma : Matrix (Fin 3) (Fin 3) ℝ := !![3/5, -4/5, 0; 4/5, 3/5, 0; 0, 0, 1]

/-- Rotation by `arccos (3/5)` about the `x`-axis. -/
def Mb : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 3/5, -4/5; 0, 4/5, 3/5]

lemma Ma_orth : Maᵀ * Ma = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ma, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> norm_num

lemma Mb_orth : Mbᵀ * Mb = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mb, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> norm_num

/-- The matrices of the two generators. -/
def genM : Fin 2 → Matrix (Fin 3) (Fin 3) ℝ := ![Ma, Mb]

lemma genM_orth : ∀ i, (genM i)ᵀ * genM i = 1 := by
  intro i; fin_cases i
  · exact Ma_orth
  · exact Mb_orth

/-- The two generating rotations, as linear isometries. -/
noncomputable def gen (i : Fin 2) : E ≃ₗᵢ[ℝ] E := rotOf (genM i) (genM_orth i)

/-- The canonical homomorphism from the free group of rank two to the rotation group. -/
noncomputable def rho : FreeGroup (Fin 2) →* (E ≃ₗᵢ[ℝ] E) := FreeGroup.lift gen

end BanachTarski

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

