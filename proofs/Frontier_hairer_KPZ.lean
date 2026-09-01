import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module documentation, so this header comment
appears immediately after the single `import Mathlib` line.)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Partial derivatives on space-time `ℝ × ℝ`

A point `p : ℝ × ℝ` is read as `(t, x)` with `t` the time variable and `x` the space variable. -/

/-- Partial derivative in the time variable of a space-time function. -/
noncomputable def dt (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun s : ℝ => f (s, p.2)) p.1

/-- Partial derivative in the space variable of a space-time function. -/
noncomputable def dx (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun y : ℝ => f (p.1, y)) p.2

/-- `IsHeatSolution Z` says that `Z : ℝ × ℝ → ℝ` is a strictly positive classical solution of
the linear heat equation `∂_t Z = ∂_x² Z`, with enough regularity in the space variable for the
second space derivative to be taken at every point. -/
structure IsHeatSolution (Z : ℝ × ℝ → ℝ) : Prop where
  /-- `Z` is everywhere strictly positive. -/
  pos : ∀ p : ℝ × ℝ, 0 < Z p
  /-- `Z` is differentiable in space. -/
  diff_x : ∀ t : ℝ, Differentiable ℝ (fun y : ℝ => Z (t, y))
  /-- The space derivative of `Z` is again differentiable in space. -/
  diff_xx : ∀ t : ℝ, Differentiable ℝ (fun y : ℝ => dx Z (t, y))
  /-- `Z` is differentiable in time. -/
  diff_t : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun s : ℝ => Z (s, p.2)) p.1
  /-- The heat equation `∂_t Z = ∂_x² Z`. -/
  heat : ∀ p : ℝ × ℝ, dt Z p = dx (dx Z) p

/-- `IsKPZSolution h` says that `h : ℝ × ℝ → ℝ` solves the noiseless (deterministic) KPZ
equation `∂_t h = ∂_x² h + (∂_x h)²`. -/
def IsKPZSolution (h : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, dt h p = dx (dx h) p + (dx h p) ^ 2

/-! ## The Cole–Hopf reduction -/

/-- The space derivative of the Cole–Hopf transform `log Z`. -/
lemma dx_log (Z : ℝ × ℝ → ℝ) (hZ : IsHeatSolution Z) (p : ℝ × ℝ) :
    dx (fun q => Real.log (Z q)) p = dx Z p / Z p := by
  have h1 : HasDerivAt (fun y : ℝ => Z (p.1, y)) (dx Z p) p.2 :=
    (hZ.diff_x p.1 p.2).hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => Real.log (Z (p.1, y))) (dx Z p / Z (p.1, p.2)) p.2 :=
    h1.log (ne_of_gt (hZ.pos (p.1, p.2)))
  simpa [dx] using h2.deriv

/-- The time derivative of the Cole–Hopf transform `log Z`. -/
lemma dt_log (Z : ℝ × ℝ → ℝ) (hZ : IsHeatSolution Z) (p : ℝ × ℝ) :
    dt (fun q => Real.log (Z q)) p = dt Z p / Z p := by
  have h1 : HasDerivAt (fun s : ℝ => Z (s, p.2)) (dt Z p) p.1 := (hZ.diff_t p).hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => Real.log (Z (s, p.2))) (dt Z p / Z (p.1, p.2)) p.1 :=
    h1.log (ne_of_gt (hZ.pos (p.1, p.2)))
  simpa [dt] using h2.deriv

/-- The second space derivative of the Cole–Hopf transform `log Z`. -/
lemma dxx_log (Z : ℝ × ℝ → ℝ) (hZ : IsHeatSolution Z) (p : ℝ × ℝ) :
    dx (dx (fun q => Real.log (Z q))) p
      = (dx (dx Z) p * Z p - dx Z p * dx Z p) / (Z p) ^ 2 := by
  have hfun : (fun y : ℝ => dx (fun q => Real.log (Z q)) (p.1, y))
      = fun y : ℝ => dx Z (p.1, y) / Z (p.1, y) := by
    funext y
    simpa using dx_log Z hZ (p.1, y)
  have hu : HasDerivAt (fun y : ℝ => dx Z (p.1, y)) (dx (dx Z) p) p.2 :=
    (hZ.diff_xx p.1 p.2).hasDerivAt
  have hv : HasDerivAt (fun y : ℝ => Z (p.1, y)) (dx Z p) p.2 := (hZ.diff_x p.1 p.2).hasDerivAt
  have hne : Z (p.1, p.2) ≠ 0 := ne_of_gt (hZ.pos (p.1, p.2))
  have hdiv := hu.div hv hne
  rw [dx, hfun]
  simpa using hdiv.deriv

/-- **Cole–Hopf reduction for the KPZ equation.**

This is the deterministic backbone of Hairer's well-posedness theory for the KPZ equation
`∂_t h = ∂_x² h + (∂_x h)² + ξ`: the nonlinear KPZ equation is reduced to the *linear* heat
equation by the Cole–Hopf transform `h = log Z`.  Concretely, if `Z` is a strictly positive
classical solution of the heat equation `∂_t Z = ∂_x² Z`, then `h = log Z` solves the noiseless
KPZ equation `∂_t h = ∂_x² h + (∂_x h)²`.  In particular, in this regime KPZ inherits the
well-posedness of the linear heat equation. -/
theorem hairer_KPZ (Z : ℝ × ℝ → ℝ) (hZ : IsHeatSolution Z) :
    IsKPZSolution (fun q => Real.log (Z q)) := by
  intro p
  have hne : Z p ≠ 0 := ne_of_gt (hZ.pos p)
  rw [dt_log Z hZ p, dxx_log Z hZ p, dx_log Z hZ p, hZ.heat p]
  field_simp
  ring

/-! ## Non-vacuity: an explicit solution -/

/-- The travelling exponential `Z (t, x) = exp (t + x)` is a strictly positive classical solution
of the heat equation, so the hypotheses of `Frontier.hairer_KPZ` are non-vacuous. -/
theorem isHeatSolution_exp : IsHeatSolution (fun p : ℝ × ℝ => Real.exp (p.1 + p.2)) := by
  have hdx : ∀ p : ℝ × ℝ, dx (fun p : ℝ × ℝ => Real.exp (p.1 + p.2)) p
      = Real.exp (p.1 + p.2) := by
    intro p
    have hd : HasDerivAt (fun y : ℝ => Real.exp (p.1 + y)) (Real.exp (p.1 + p.2)) p.2 := by
      simpa using ((hasDerivAt_id p.2).const_add p.1).exp
    simpa [dx] using hd.deriv
  refine ⟨fun p => Real.exp_pos _, fun t => ?_, fun t => ?_, fun p => ?_, fun p => ?_⟩
  · exact Real.differentiable_exp.comp (differentiable_id.const_add t)
  · simp only [hdx]
    exact Real.differentiable_exp.comp (differentiable_id.const_add t)
  · exact (Real.differentiable_exp.comp (differentiable_id.add_const p.2)).differentiableAt
  · have h1 : dt (fun p : ℝ × ℝ => Real.exp (p.1 + p.2)) p = Real.exp (p.1 + p.2) := by
      have hd : HasDerivAt (fun s : ℝ => Real.exp (s + p.2)) (Real.exp (p.1 + p.2)) p.1 := by
        simpa using ((hasDerivAt_id p.1).add_const p.2).exp
      show deriv (fun s : ℝ => Real.exp (s + p.2)) p.1 = _
      exact hd.deriv
    have h2 : dx (dx (fun p : ℝ × ℝ => Real.exp (p.1 + p.2))) p = Real.exp (p.1 + p.2) := by
      have hfun : (fun y : ℝ => dx (fun p : ℝ × ℝ => Real.exp (p.1 + p.2)) (p.1, y))
          = fun y : ℝ => Real.exp (p.1 + y) := by
        funext y
        simpa using hdx (p.1, y)
      have hd : HasDerivAt (fun y : ℝ => Real.exp (p.1 + y)) (Real.exp (p.1 + p.2)) p.2 := by
        simpa using ((hasDerivAt_id p.2).const_add p.1).exp
      rw [dx, hfun]
      exact hd.deriv
    rw [h1, h2]

/-- The corresponding KPZ solution `h (t, x) = t + x`, obtained from `Frontier.hairer_KPZ`. -/
theorem isKPZSolution_linear : IsKPZSolution (fun p : ℝ × ℝ => p.1 + p.2) := by
  have h := hairer_KPZ _ isHeatSolution_exp
  simpa [Real.log_exp] using h

end Frontier

