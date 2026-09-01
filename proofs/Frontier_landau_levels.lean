/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module doc-comment, so the header above is
-- reproduced verbatim as a module doc-comment immediately after the import.)
import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Polynomial

/-! ## Hermite polynomials over `ℝ` -/

/-- The (probabilists') Hermite polynomials, with real coefficients. -/
noncomputable def hermiteR (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

lemma hermiteR_zero : hermiteR 0 = 1 := by
  simp [hermiteR, Polynomial.hermite_zero]

lemma hermiteR_one : hermiteR 1 = X := by
  simp [hermiteR, Polynomial.hermite_one]

lemma hermiteR_succ (n : ℕ) :
    hermiteR (n + 1) = X * hermiteR n - derivative (hermiteR n) := by
  simp [hermiteR, Polynomial.hermite_succ, Polynomial.derivative_map]

/-- `He_{n+1}' = (n+1) He_n`. -/
lemma derivative_hermiteR (n : ℕ) :
    derivative (hermiteR (n + 1)) = C ((n : ℝ) + 1) * hermiteR n := by
  induction n with
  | zero => simp [hermiteR_one, hermiteR_zero]
  | succ n ih =>
      rw [hermiteR_succ (n + 1)]
      rw [derivative_sub, derivative_mul, derivative_X, ih]
      rw [derivative_C_mul]
      have h : hermiteR (n + 1) = X * hermiteR n - derivative (hermiteR n) := hermiteR_succ n
      push_cast
      rw [h]
      ring
  
/-- The Hermite differential equation `He_n'' - x He_n' + n He_n = 0`. -/
lemma hermiteR_ode (n : ℕ) :
    derivative (derivative (hermiteR n)) - X * derivative (hermiteR n)
      + C (n : ℝ) * hermiteR n = 0 := by
  have h1 : derivative (hermiteR (n + 1)) = C ((n : ℝ) + 1) * hermiteR n := derivative_hermiteR n
  have h2 : hermiteR (n + 1) = X * hermiteR n - derivative (hermiteR n) := hermiteR_succ n
  rw [h2, derivative_sub, derivative_mul, derivative_X] at h1
  have hC : C ((n : ℝ) + 1) = C (n : ℝ) + 1 := by push_cast; ring
  rw [hC] at h1
  linear_combination -h1

/-! ## Gaussian-weighted derivative -/

/-- The polynomial factor obtained by differentiating `p(t) e^{-t²/4}`. -/
noncomputable def gDeriv (p : Polynomial ℝ) : Polynomial ℝ :=
  derivative p - C (1 / 2) * (X * p)

lemma gDeriv_gDeriv_hermiteR (n : ℕ) :
    gDeriv (gDeriv (hermiteR n))
      = (C (1 / 4) * X ^ 2 - C (n : ℝ) - C (1 / 2)) * hermiteR n := by
  have h := hermiteR_ode n
  simp only [gDeriv, derivative_sub, derivative_mul, derivative_X, derivative_C, Polynomial.map_one]
  linear_combination h

/-! ## The Hermite functions -/

/-- The `n`-th Hermite function `He_n(t) e^{-t²/4}` (unnormalised). -/
noncomputable def hermiteGauss (n : ℕ) (t : ℝ) : ℝ :=
  eval t (hermiteR n) * Real.exp (-(t ^ 2 / 4))

lemma hasDerivAt_polyGauss (p : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => eval u p * Real.exp (-(u ^ 2 / 4)))
      (eval t (gDeriv p) * Real.exp (-(t ^ 2 / 4))) t := by
  have h1 : HasDerivAt (fun u : ℝ => eval u p) (eval t (derivative p)) t := p.hasDerivAt t
  have h2 : HasDerivAt (fun u : ℝ => -(u ^ 2 / 4)) (-(t / 2)) t := by
    have := ((hasDerivAt_pow 2 t).div_const 4).neg
    simpa using this
  have h3 := h2.exp
  have := h1.mul h3
  convert this using 1
  simp [gDeriv]
  ring

lemma hasDerivAt_hermiteGauss (n : ℕ) (t : ℝ) :
    HasDerivAt (hermiteGauss n) (eval t (gDeriv (hermiteR n)) * Real.exp (-(t ^ 2 / 4))) t :=
  hasDerivAt_polyGauss (hermiteR n) t

lemma hasDerivAt_hermiteGauss' (n : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => eval u (gDeriv (hermiteR n)) * Real.exp (-(u ^ 2 / 4)))
      ((t ^ 2 / 4 - ((n : ℝ) + 1 / 2)) * hermiteGauss n t) t := by
  have h := hasDerivAt_polyGauss (gDeriv (hermiteR n)) t
  rw [gDeriv_gDeriv_hermiteR n] at h
  convert h using 1
  simp [hermiteGauss]
  ring

end Frontier

