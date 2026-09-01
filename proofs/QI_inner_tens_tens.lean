import Mathlib

/-!
# The no-deleting theorem

We model a finite-dimensional quantum system by `EuclideanSpace ℂ ι` and the tensor product
of two such systems by `EuclideanSpace ℂ (ι × κ)`, with the product state `tens x y` given
by `(tens x y) (i, j) = x i * y j`.

A *deleting machine* would be a unitary `U` acting on (system) ⊗ (system) ⊗ (ancilla) such
that, for every unit state `ψ`,
`U (ψ ⊗ ψ ⊗ a) = ψ ⊗ blank ⊗ a'`,
i.e. the second copy of `ψ` is erased and replaced by a fixed *blank* state, while the
ancilla ends up in a fixed state `a'` (independent of `ψ`).

`QI.no_deleting` shows no such unitary exists.
-/

namespace QI

/-- The product (tensor) of two finite-dimensional state vectors. -/
noncomputable def tens {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) : EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 (fun p : ι × κ => x p.1 * y p.2)

/-- Inner products of product states multiply. -/
theorem inner_tens_tens {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x x' : EuclideanSpace ℂ ι) (y y' : EuclideanSpace ℂ κ) :
    inner ℂ (tens x y) (tens x' y') = inner ℂ x x' * inner ℂ y y' := by
  simp only [tens, PiLp.inner_apply, Fintype.sum_prod_type,
    RCLike.inner_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The state `|0⟩` of a qubit. -/
noncomputable def ket0 : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

/-- The qubit state `(3/5)|0⟩ + (4/5)|1⟩`. -/
noncomputable def ketD : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![3/5, 4/5]

theorem norm_ket0 : ‖ket0‖ = 1 := by
  simp [ket0]

theorem norm_ketD : ‖ketD‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [ketD, Fin.sum_univ_two, Complex.norm_def, Complex.normSq_apply]

theorem inner_ket0_ket0 : inner ℂ ket0 ket0 = 1 := by
  simp [ket0]

theorem inner_ket0_ketD : inner ℂ ket0 ketD = (3/5 : ℂ) := by
  simp [ket0, ketD, PiLp.inner_apply, RCLike.inner_apply,
    EuclideanSpace.single_apply]

/-- **No-deleting theorem.** There is no unitary `U` on
(system) ⊗ (system) ⊗ (ancilla) which, for every unit state `ψ`, maps `ψ ⊗ ψ ⊗ a` to
`ψ ⊗ blank ⊗ a'`, where the blank state `blank` and the final ancilla state `a'` do not
depend on `ψ`.  In other words, an unknown quantum state cannot be deleted. -/
theorem no_deleting {α : Type*} [Fintype α]
    (blank : EuclideanSpace ℂ (Fin 2)) (a a' : EuclideanSpace ℂ α) (ha : ‖a‖ = 1)
    (U : EuclideanSpace ℂ (Fin 2 × Fin 2 × α) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2 × Fin 2 × α)) :
    ¬ ∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
        U (tens psi (tens psi a)) = tens psi (tens blank a') := by
  intro hU
  have hinner : inner ℂ a a = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ha]; norm_num
  -- the fundamental relation: `⟪ψ,φ⟫ ^ 2 = ⟪ψ,φ⟫ * c` with `c = ⟪blank,blank⟫ * ⟪a',a'⟫`
  set c : ℂ := inner ℂ blank blank * inner ℂ a' a' with hc
  have key : ∀ psi phi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 → ‖phi‖ = 1 →
      inner ℂ psi phi * inner ℂ psi phi = inner ℂ psi phi * c := by
    intro psi phi hp hq
    have h : inner ℂ (U (tens psi (tens psi a))) (U (tens phi (tens phi a)))
        = inner ℂ (tens psi (tens blank a')) (tens phi (tens blank a')) := by
      rw [hU psi hp, hU phi hq]
    rw [U.inner_map_map] at h
    simp only [inner_tens_tens, hinner, mul_one] at h
    rw [h, hc]
  have h1 : (1 : ℂ) = c := by
    have := key ket0 ket0 norm_ket0 norm_ket0
    rw [inner_ket0_ket0] at this
    simpa using this
  have h2 := key ket0 ketD norm_ket0 norm_ketD
  rw [inner_ket0_ketD, ← h1] at h2
  norm_num at h2

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

