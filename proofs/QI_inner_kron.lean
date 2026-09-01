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

/-!
# The no-deleting theorem

Given two copies of an arbitrary unknown quantum state, it is impossible to delete one of
them by a unitary evolution of the composite system (system + system + ancilla).

We model the qubit Hilbert space by `EuclideanSpace ℂ (Fin 2)`, the ancilla by
`EuclideanSpace ℂ ι` for an arbitrary finite index type `ι`, and the composite system
`H ⊗ H ⊗ A` by `EuclideanSpace ℂ (Fin 2 × Fin 2 × ι)`.  The tensor product of vectors is
`QI.kron`, and `QI.tri x y z` is the threefold tensor product `x ⊗ y ⊗ z`.

The proof is the standard inner-product argument: a linear isometry preserves inner
products, so if `ψ ⊗ ψ ⊗ anc` were mapped to `ψ ⊗ blank ⊗ out` with `blank` and `out`
independent of `ψ`, then for all unit vectors `ψ`, `φ` one would get
`⟪ψ, φ⟫ * ⟪blank, blank⟫ * ⟪out, out⟫ = ⟪ψ, φ⟫ ^ 2 * ⟪anc, anc⟫`.  Taking `ψ = φ` shows
`⟪blank, blank⟫ * ⟪out, out⟫ = ⟪anc, anc⟫`, and then a pair of states with
`⟪ψ, φ⟫ = 3 / 5` forces `⟪anc, anc⟫ = 0`, i.e. `anc = 0`.
-/

namespace QI

/-- The tensor product `u ⊗ v` of two vectors, realized concretely as a vector indexed by
the product of the index types. -/
noncomputable def kron {α β : Type*} [Fintype α] [Fintype β]
    (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) : EuclideanSpace ℂ (α × β) :=
  WithLp.toLp 2 (fun p => u p.1 * v p.2)

/-- Inner products factor over the tensor product. -/
theorem inner_kron {α β : Type*} [Fintype α] [Fintype β]
    (u u' : EuclideanSpace ℂ α) (v v' : EuclideanSpace ℂ β) :
    (inner ℂ (kron u v) (kron u' v') : ℂ) = (inner ℂ u u' : ℂ) * (inner ℂ v v' : ℂ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, kron, Fintype.sum_prod_type, map_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The threefold tensor product `x ⊗ y ⊗ z` of two qubit states and an ancilla state. -/
noncomputable def tri {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ (Fin 2)) (z : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Fin 2 × Fin 2 × ι) :=
  kron x (kron y z)

/-- Inner products factor over the threefold tensor product. -/
theorem inner_tri {ι : Type*} [Fintype ι]
    (x y x' y' : EuclideanSpace ℂ (Fin 2)) (z z' : EuclideanSpace ℂ ι) :
    (inner ℂ (tri x y z) (tri x' y' z') : ℂ)
      = (inner ℂ x x' : ℂ) * (inner ℂ y y' : ℂ) * (inner ℂ z z' : ℂ) := by
  rw [tri, tri, inner_kron, inner_kron, mul_assoc]

/-- The qubit state `|0⟩`. -/
noncomputable def qubit0 : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]

/-- The qubit state `(3 |0⟩ + 4 |1⟩) / 5`. -/
noncomputable def qubit35 : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![3 / 5, 4 / 5]

theorem norm_qubit0 : ‖qubit0‖ = 1 := by
  have h : ∑ i, ‖(qubit0 i : ℂ)‖ ^ 2 = 1 := by
    norm_num [qubit0, Fin.sum_univ_two, PiLp.toLp_apply]
  rw [EuclideanSpace.norm_eq, h, Real.sqrt_one]

theorem norm_qubit35 : ‖qubit35‖ = 1 := by
  have h : ∑ i, ‖(qubit35 i : ℂ)‖ ^ 2 = 1 := by
    norm_num [qubit35, Fin.sum_univ_two, PiLp.toLp_apply]
  rw [EuclideanSpace.norm_eq, h, Real.sqrt_one]

theorem inner_qubit0_self : (inner ℂ qubit0 qubit0 : ℂ) = 1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, qubit0, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem inner_qubit0_qubit35 : (inner ℂ qubit0 qubit35 : ℂ) = 3 / 5 := by
  norm_num [qubit0, qubit35, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two,
    PiLp.toLp_apply]

/-- **No-deleting theorem**, isometric version.  There is no linear isometry `U` of
`H ⊗ H ⊗ A` (with `H` a qubit and `A` an arbitrary finite-dimensional ancilla), no
"blank" state `blank` and no final ancilla state `out` such that `U` maps `ψ ⊗ ψ ⊗ anc`
to `ψ ⊗ blank ⊗ out` for every unit vector `ψ`, unless the initial ancilla state `anc`
is `0`. -/
theorem no_deleting_isometry {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ (Fin 2 × Fin 2 × ι) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2 × Fin 2 × ι))
    (anc : EuclideanSpace ℂ ι) (hanc : anc ≠ 0)
    (blank : EuclideanSpace ℂ (Fin 2)) (out : EuclideanSpace ℂ ι)
    (hdel : ∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
      U (tri psi psi anc) = tri psi blank out) :
    False := by
  have key : ∀ x y : EuclideanSpace ℂ (Fin 2), ‖x‖ = 1 → ‖y‖ = 1 →
      (inner ℂ x y : ℂ) * (inner ℂ blank blank : ℂ) * (inner ℂ out out : ℂ)
        = (inner ℂ x y : ℂ) * (inner ℂ x y : ℂ) * (inner ℂ anc anc : ℂ) := by
    intro x y hx hy
    have h := U.inner_map_map (tri x x anc) (tri y y anc)
    rw [hdel x hx, hdel y hy, inner_tri, inner_tri] at h
    exact h
  have h1 := key qubit0 qubit0 norm_qubit0 norm_qubit0
  have h2 := key qubit0 qubit35 norm_qubit0 norm_qubit35
  rw [inner_qubit0_self] at h1
  rw [inner_qubit0_qubit35] at h2
  have hBO : (inner ℂ blank blank : ℂ) * (inner ℂ out out : ℂ) = (inner ℂ anc anc : ℂ) := by
    linear_combination h1
  have hA : (inner ℂ anc anc : ℂ) = 0 := by
    linear_combination ((25 : ℂ) / 6) * h2 - ((5 : ℂ) / 2) * hBO
  exact hanc (inner_self_eq_zero.mp hA)

/-- **No-deleting theorem**.  There is no unitary `U` of `H ⊗ H ⊗ A` (with `H` a qubit and
`A` an arbitrary finite-dimensional ancilla), no "blank" state `blank` and no final
ancilla state `out` such that `U` deletes one of two copies of an arbitrary unknown state,
i.e. maps `ψ ⊗ ψ ⊗ anc` to `ψ ⊗ blank ⊗ out` for every unit vector `ψ`, the final ancilla
state `out` being independent of `ψ`, unless the initial ancilla state `anc` is `0`. -/
theorem no_deleting {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ (Fin 2 × Fin 2 × ι) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2 × Fin 2 × ι))
    (anc : EuclideanSpace ℂ ι) (hanc : anc ≠ 0)
    (blank : EuclideanSpace ℂ (Fin 2)) (out : EuclideanSpace ℂ ι)
    (hdel : ∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
      U (tri psi psi anc) = tri psi blank out) :
    False :=
  no_deleting_isometry U.toLinearIsometry anc hanc blank out hdel

end QI

#print axioms QI.no_deleting
#print axioms QI.no_deleting_isometry

