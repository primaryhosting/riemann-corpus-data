import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped InnerProductSpace

namespace Phys

/--
**Kramers degeneracy.**

Setting: a finite-dimensional complex inner product space `V` (the state space),
a Hamiltonian `H : V →ₗ[ℂ] V`, and a time-reversal operator `T`, modelled as a
conjugate-linear (semilinear over `starRingEnd ℂ`) map which is antiunitary
(`⟪T x, T y⟫ = ⟪y, x⟫`) and squares to `-1` (`T (T x) = -x`), the latter being the
hallmark of half-integer spin. Time-reversal invariance is `H ∘ T = T ∘ H`.

Conclusion: every (real) energy level `E` of `H` that is actually attained has
eigenspace of dimension at least `2`, i.e. the levels are (at least) doubly degenerate.
-/
theorem kramers_degeneracy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ⋆[ℂ] V) (H : V →ₗ[ℂ] V)
    (hT_anti : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hT_sq : ∀ x : V, T (T x) = -x)
    (hcomm : ∀ x : V, H (T x) = T (H x))
    (E : ℝ) (ψ : V) (hψ : ψ ≠ 0) (heig : H ψ = (E : ℂ) • ψ) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace H (E : ℂ)) := by
  -- `T ψ` is an eigenvector for the same (real) eigenvalue.
  have hTeig : H (T ψ) = (E : ℂ) • T ψ := by
    have : H (T ψ) = T (H ψ) := hcomm ψ
    rw [this, heig, map_smulₛₗ]
    simp
  -- `T ψ ≠ 0`, since `T (T ψ) = -ψ ≠ 0`.
  have hTψ : T ψ ≠ 0 := by
    intro h
    apply hψ
    have := hT_sq ψ
    rw [h, map_zero] at this
    simpa [eq_comm, neg_eq_zero] using this.symm
  -- `ψ` and `T ψ` are orthogonal.
  have horth : ⟪T ψ, ψ⟫_ℂ = 0 := by
    have h := hT_anti ψ (T ψ)
    rw [hT_sq ψ, inner_neg_right] at h
    linear_combination -h / 2
  have horth' : ⟪ψ, T ψ⟫_ℂ = 0 := by
    rw [← inner_conj_symm, horth, map_zero]
  -- Hence they are linearly independent.
  have hli : LinearIndependent ℂ ![ψ, T ψ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    constructor
    · have h1 : ⟪ψ, s • ψ + t • T ψ⟫_ℂ = 0 := by rw [hst, inner_zero_right]
      rw [inner_add_right, inner_smul_right, inner_smul_right, horth'] at h1
      simpa [hψ] using h1
    · have h1 : ⟪T ψ, s • ψ + t • T ψ⟫_ℂ = 0 := by rw [hst, inner_zero_right]
      rw [inner_add_right, inner_smul_right, inner_smul_right, horth] at h1
      simpa [hTψ] using h1
  -- Both lie in the eigenspace, so the eigenspace has dimension at least two.
  set W := Module.End.eigenspace H (E : ℂ)
  have hψW : ψ ∈ W := Module.End.mem_eigenspace_iff.2 heig
  have hTψW : T ψ ∈ W := Module.End.mem_eigenspace_iff.2 hTeig
  have hli2 : LinearIndependent ℂ ![(⟨ψ, hψW⟩ : W), ⟨T ψ, hTψW⟩] := by
    apply LinearIndependent.of_comp W.subtype
    convert hli using 1
    ext i
    fin_cases i <;> rfl
  simpa using hli2.fintype_card_le_finrank

end Phys

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

