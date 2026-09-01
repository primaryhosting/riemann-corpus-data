/-
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- **Goldstone's theorem** (classical/field-theoretic version, in its finite-dimensional
"mass matrix" form).

Setting: a potential `V` on a real normed space `E`, of class `C²`, invariant under a
continuous one-parameter group of global symmetries whose infinitesimal generator is the
continuous linear map `K`.  Infinitesimal invariance of the potential says that the
derivative of `V` vanishes along the generating vector field, i.e.
`fderiv ℝ V x (K x) = 0` for every `x`.

A vacuum is a local minimum `v` of `V`.  The symmetry is *spontaneously broken* at `v` when
the vacuum is not invariant, i.e. the generator moves it: `K v ≠ 0`.

Conclusion: the mass matrix — the Hessian `H = D(DV)(v)` of `V` at the vacuum — annihilates
the nonzero direction `K v`: for every `u`, `H u (K v) = 0`.  Thus the fluctuation mode along
the broken symmetry direction has zero mass: a Goldstone boson.

Proof: differentiate the identity `x ↦ (DV x) (K x) = 0` at `v`, using `DV v = 0` (first-order
condition at the minimum). -/
theorem goldstone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (K : E →L[ℝ] E) (v : E)
    (hV : ContDiff ℝ 2 V)
    (hinv : ∀ x, fderiv ℝ V x (K x) = 0)
    (hmin : IsLocalMin V v)
    (hbroken : K v ≠ 0) :
    ∃ w : E, w ≠ 0 ∧ ∀ u : E, (fderiv ℝ (fun x => fderiv ℝ V x) v) u w = 0 := by
  refine ⟨K v, hbroken, ?_⟩
  -- first-order condition at the vacuum
  have hcrit : fderiv ℝ V v = 0 := hmin.fderiv_eq_zero
  -- `x ↦ fderiv ℝ V x` is differentiable
  have hD : Differentiable ℝ (fun x => fderiv ℝ V x) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  -- derivative of `x ↦ (DV x) (K x)` at `v`
  have hprod : HasFDerivAt (fun x => (fderiv ℝ V x) (K x))
      (((fderiv ℝ V v).comp (K : E →L[ℝ] E)) +
        (fderiv ℝ (fun x => fderiv ℝ V x) v).flip (K v)) v :=
    (hD v).hasFDerivAt.clm_apply (K.hasFDerivAt)
  -- but that function is identically zero
  have hzero : HasFDerivAt (fun x => (fderiv ℝ V x) (K x)) (0 : E →L[ℝ] ℝ) v := by
    have : (fun x => (fderiv ℝ V x) (K x)) = fun _ : E => (0 : ℝ) := funext hinv
    rw [this]
    exact hasFDerivAt_const _ _
  have heq := hprod.unique hzero
  intro u
  have := congrArg (fun L : E →L[ℝ] ℝ => L u) heq
  simpa [hcrit] using this

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

