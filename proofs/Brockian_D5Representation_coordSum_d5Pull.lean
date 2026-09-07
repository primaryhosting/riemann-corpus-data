/-
  Brockian/D5Representation.lean

  First representation-theoretic consequences of the completed
  `Aut(C5) ~= D5` theorem.

  This file deliberately stays finite and local: it builds the permutation
  representation on vertex functions `Fin 5 -> C`, proves that constants are
  fixed, and proves that the zero-sum hyperplane is invariant.  This gives the
  next agents a stable foothold for character/isotypic-projector work without
  reopening the automorphism enumeration proof.
-/
import Mathlib
import Brockian.AutomorphismFull

open BigOperators
open DihedralGroup
open Brockian.Automorphism
open Brockian.Automorphism.Full

namespace Brockian.D5Representation

/-- Complex-valued functions on the vertices of the 5-cycle. -/
abbrev VertexSpace := Fin 5 → ℂ

/-- The constant vector with value `c` on every vertex. -/
def constantVector (c : ℂ) : VertexSpace := fun _ => c

/-- Linear map `c |->` the constant vector with value `c`. -/
def constantLinear : ℂ →ₗ[ℂ] VertexSpace where
  toFun := constantVector
  map_add' := by intro c d; rfl
  map_smul' := by intro c d; rfl

@[simp] theorem constantLinear_apply (c : ℂ) :
    constantLinear c = constantVector c := rfl

/-- The one-dimensional constant subspace of vertex functions. -/
def constantLine : Submodule ℂ VertexSpace :=
  LinearMap.range constantLinear

/-- Coordinate sum on `Fin 5 -> C`. -/
def coordSum (f : VertexSpace) : ℂ :=
  ∑ x : Fin 5, f x

/-- Coordinate sum as a linear functional. -/
def coordSumLinear : VertexSpace →ₗ[ℂ] ℂ where
  toFun := coordSum
  map_add' := by intro f g; simp [coordSum, Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    simpa [coordSum] using
      (Finset.smul_sum (s := Finset.univ) (f := fun x : Fin 5 => f x) (r := c)).symm

@[simp] theorem coordSumLinear_apply (f : VertexSpace) :
    coordSumLinear f = coordSum f := rfl

/-- The standard zero-sum hyperplane. -/
def zeroSumSubmodule : Submodule ℂ VertexSpace :=
  LinearMap.ker coordSumLinear

/-- Pullback of vertex functions by a graph automorphism of `C5`. -/
noncomputable def autPull (σ : C5 ≃g C5) : VertexSpace ≃ₗ[ℂ] VertexSpace where
  toFun f := fun x => f (σ.symm x)
  invFun f := fun x => f (σ x)
  left_inv f := by
    funext x
    simp
  right_inv f := by
    funext x
    simp
  map_add' f g := by
    funext x
    rfl
  map_smul' c f := by
    funext x
    rfl

@[simp] theorem autPull_apply (σ : C5 ≃g C5) (f : VertexSpace) (x : Fin 5) :
    autPull σ f x = f (σ.symm x) := rfl

/-- The `D5` action on vertex functions, transported through
`dihedralHom : D5 -> Aut(C5)`. -/
noncomputable def d5Pull (g : DihedralGroup 5) : VertexSpace ≃ₗ[ℂ] VertexSpace :=
  autPull (dihedralHom g)

@[simp] theorem d5Pull_apply (g : DihedralGroup 5) (f : VertexSpace) (x : Fin 5) :
    d5Pull g f x = f ((dihedralHom g).symm x) := rfl

/-- The completed automorphism theorem is available as a representation-theory input. -/
noncomputable def d5AutEquiv : DihedralGroup 5 ≃* (C5 ≃g C5) :=
  autEquivDihedral

/-! ### Constants are fixed -/

theorem autPull_constant (σ : C5 ≃g C5) (c : ℂ) :
    autPull σ (constantVector c) = constantVector c := by
  funext x
  rfl

theorem d5Pull_constant (g : DihedralGroup 5) (c : ℂ) :
    d5Pull g (constantVector c) = constantVector c :=
  autPull_constant (dihedralHom g) c

theorem autPull_mem_constantLine (σ : C5 ≃g C5) {f : VertexSpace}
    (hf : f ∈ constantLine) :
    autPull σ f ∈ constantLine := by
  rcases hf with ⟨c, rfl⟩
  exact ⟨c, by rw [constantLinear_apply, autPull_constant]⟩

theorem d5Pull_mem_constantLine (g : DihedralGroup 5) {f : VertexSpace}
    (hf : f ∈ constantLine) :
    d5Pull g f ∈ constantLine :=
  autPull_mem_constantLine (dihedralHom g) hf

/-! ### Coordinate sum and zero-sum invariance -/

theorem coordSum_autPull (σ : C5 ≃g C5) (f : VertexSpace) :
    coordSum (autPull σ f) = coordSum f := by
  unfold coordSum
  exact σ.toEquiv.symm.sum_comp f

theorem coordSum_d5Pull (g : DihedralGroup 5) (f : VertexSpace) :
    coordSum (d5Pull g f) = coordSum f :=
  coordSum_autPull (dihedralHom g) f

theorem autPull_mem_zeroSumSubmodule (σ : C5 ≃g C5) {f : VertexSpace}
    (hf : f ∈ zeroSumSubmodule) :
    autPull σ f ∈ zeroSumSubmodule := by
  change coordSumLinear (autPull σ f) = 0
  rw [coordSumLinear_apply, coordSum_autPull]
  exact hf

theorem d5Pull_mem_zeroSumSubmodule (g : DihedralGroup 5) {f : VertexSpace}
    (hf : f ∈ zeroSumSubmodule) :
    d5Pull g f ∈ zeroSumSubmodule :=
  autPull_mem_zeroSumSubmodule (dihedralHom g) hf

theorem coordSum_constantVector (c : ℂ) :
    coordSum (constantVector c) = (5 : ℂ) * c := by
  simp [coordSum, constantVector]

theorem constantVector_mem_zeroSumSubmodule_iff (c : ℂ) :
    constantVector c ∈ zeroSumSubmodule ↔ c = 0 := by
  constructor
  · intro h
    change coordSumLinear (constantVector c) = 0 at h
    rw [coordSumLinear_apply, coordSum_constantVector] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · intro h
    rw [h]
    change coordSumLinear (constantVector 0) = 0
    simp [coordSumLinear, coordSum, constantVector]

end Brockian.D5Representation
