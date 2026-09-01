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

open scoped InnerProductSpace

namespace QPhys

/-- **Every eigenvalue of a Hermitian operator is real.**

If `T` is a linear operator on a complex inner product space that is Hermitian
(symmetric: `⟪T x, y⟫ = ⟪x, T y⟫` for all `x y`), and `mu` is an eigenvalue of `T`
with eigenvector `v ≠ 0`, then `mu` is real, i.e. `mu.im = 0`. -/
theorem hermitian_real_spectrum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →ₗ[ℂ] E)
    (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (mu : ℂ) (v : E) (hv : v ≠ 0) (hTv : T v = mu • v) :
    mu.im = 0 := by
  have h := hT v v
  rw [hTv, inner_smul_left, inner_smul_right] at h
  have hn : (⟪v, v⟫_ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  have hc : (starRingEnd ℂ) mu = mu := mul_right_cancel₀ hn h
  exact Complex.conj_eq_iff_im.mp hc

end QPhys

