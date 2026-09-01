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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-- The **Berry curvature** of a Berry connection one-form `A = (A₁, A₂)` on the two-dimensional
parameter plane `ℝ × ℝ`: `F = ∂₁ A₂ - ∂₂ A₁`, the exterior derivative of the connection. -/
noncomputable def berryCurvature (A : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ => (A q).2) p (1, 0) -
    fderiv ℝ (fun q : ℝ × ℝ => (A q).1) p (0, 1)

/-- The **Berry phase** accumulated along the closed rectangular loop with corners
`(a₁, a₂)`, `(b₁, a₂)`, `(b₁, b₂)`, `(a₁, b₂)`, traversed counterclockwise: the line
integral `∮ A · dl` of the Berry connection along the four edges of the rectangle. -/
noncomputable def berryPhaseRect (A : ℝ × ℝ → ℝ × ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ((∫ x in a₁..b₁, (A (x, a₂)).1) + ∫ y in a₂..b₂, (A (b₁, y)).2) -
    ((∫ x in a₁..b₁, (A (x, b₂)).1) + ∫ y in a₂..b₂, (A (a₁, y)).2)

/-- **The Berry phase around a closed loop is the integral of the Berry curvature**
(base case: a rectangular loop in the parameter plane).

For a continuously differentiable Berry connection `A = (A₁, A₂)` on `ℝ × ℝ`, the Berry phase
`∮ A · dl` accumulated around the boundary of the rectangle `[a₁, b₁] × [a₂, b₂]` equals the
integral of the Berry curvature `F = ∂₁A₂ - ∂₂A₁` over the enclosed region.  Quantization of
the total Berry flux over a closed surface is the global consequence of this local identity. -/
theorem berry_phase_quantized (A : ℝ × ℝ → ℝ × ℝ) (hA : ContDiff ℝ 1 A) (a₁ a₂ b₁ b₂ : ℝ) :
    berryPhaseRect A a₁ a₂ b₁ b₂ =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y) := by
  have hc1 : ContDiff ℝ 1 (fun q : ℝ × ℝ => (A q).1) := hA.fst
  have hc2 : ContDiff ℝ 1 (fun q : ℝ × ℝ => (A q).2) := hA.snd
  have hd1 : Differentiable ℝ (fun q : ℝ × ℝ => (A q).1) := hc1.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fun q : ℝ × ℝ => (A q).2) := hc2.differentiable (by norm_num)
  have Hdf : ∀ p : ℝ × ℝ,
      HasFDerivAt (fun q : ℝ × ℝ => (A q).2) (fderiv ℝ (fun q : ℝ × ℝ => (A q).2) p) p :=
    fun p => (hd2 p).hasFDerivAt
  have Hdg : ∀ p : ℝ × ℝ,
      HasFDerivAt (fun q : ℝ × ℝ => -(A q).1) (-fderiv ℝ (fun q : ℝ × ℝ => (A q).1) p) p :=
    fun p => ((hd1 p).hasFDerivAt).neg
  have hdivcont : Continuous fun p : ℝ × ℝ =>
      fderiv ℝ (fun q : ℝ × ℝ => (A q).2) p (1, 0) +
        (-fderiv ℝ (fun q : ℝ × ℝ => (A q).1) p) (0, 1) := by
    have h1 : Continuous fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => (A q).2) p (1, 0) :=
      (hc2.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have h2 : Continuous fun p : ℝ × ℝ => (-fderiv ℝ (fun q : ℝ × ℝ => (A q).1) p) (0, 1) := by
      simpa using
        (((hc1.continuous_fderiv (by norm_num)).clm_apply continuous_const).neg :
          Continuous fun p : ℝ × ℝ => -(fderiv ℝ (fun q : ℝ × ℝ => (A q).1) p (0, 1)))
    exact h1.add h2
  have Hi : IntegrableOn (fun p : ℝ × ℝ =>
      fderiv ℝ (fun q : ℝ × ℝ => (A q).2) p (1, 0) +
        (-fderiv ℝ (fun q : ℝ × ℝ => (A q).1) p) (0, 1)) (uIcc a₁ b₁ ×ˢ uIcc a₂ b₂) :=
    hdivcont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (fun q : ℝ × ℝ => (A q).2) (fun q : ℝ × ℝ => -(A q).1)
    (fun p => fderiv ℝ (fun q : ℝ × ℝ => (A q).2) p)
    (fun p => -fderiv ℝ (fun q : ℝ × ℝ => (A q).1) p) a₁ a₂ b₁ b₂
    (hc2.continuous.continuousOn) (hc1.continuous.neg.continuousOn)
    (fun p _ => Hdf p) (fun p _ => Hdg p) Hi
  have hcurv : ∀ x y : ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => (A q).2) (x, y) (1, 0) +
        (-fderiv ℝ (fun q : ℝ × ℝ => (A q).1) (x, y)) (0, 1) = berryCurvature A (x, y) := by
    intro x y
    simp [berryCurvature, sub_eq_add_neg]
  simp only [hcurv] at key
  rw [berryPhaseRect, key]
  simp only [intervalIntegral.integral_neg]
  ring

end Frontier

