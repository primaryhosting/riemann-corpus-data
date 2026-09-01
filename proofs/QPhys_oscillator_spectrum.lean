/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

set_option autoImplicit false

namespace QPhys

open Polynomial

section Oscillator

variable (m ω hbar : ℝ)

/-- The Gaussian ground-state profile `exp (-m ω x² / (2ℏ))`. -/
noncomputable def gauss (x : ℝ) : ℝ := Real.exp (-(m * ω / (2 * hbar)) * x ^ 2)

/-- A state of the form (polynomial) × (Gaussian). -/
noncomputable def stateFun (p : Polynomial ℝ) : ℝ → ℝ :=
  fun x => p.eval x * gauss m ω hbar x

/-- The harmonic-oscillator Hamiltonian `H = -ℏ²/(2m) d²/dx² + ½ m ω² x²`. -/
noncomputable def hamiltonian (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -(hbar ^ 2 / (2 * m)) * deriv (deriv f) x + (1 / 2) * m * ω ^ 2 * x ^ 2 * f x

/-- The creation (raising) ladder operator `a† = (mωx - ℏ d/dx)/√(2mℏω)`. -/
noncomputable def raise (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (m * ω * x * f x - hbar * deriv f x) / Real.sqrt (2 * m * hbar * ω)

/-- The annihilation (lowering) ladder operator `a = (mωx + ℏ d/dx)/√(2mℏω)`. -/
noncomputable def lower (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (m * ω * x * f x + hbar * deriv f x) / Real.sqrt (2 * m * hbar * ω)

/-- Polynomial-level differentiation operator: if `f = p·gauss` then `f' = (Dpoly p)·gauss`. -/
noncomputable def Dpoly (p : Polynomial ℝ) : Polynomial ℝ :=
  derivative p - Polynomial.C (m * ω / hbar) * (X * p)

/-- Polynomial-level raising operator: `a†(p·gauss) = const · (upPoly p)·gauss`. -/
noncomputable def upPoly (p : Polynomial ℝ) : Polynomial ℝ :=
  X * p - Polynomial.C (hbar / (2 * m * ω)) * derivative p

/-- Polynomial-level Hamiltonian (divided by `ℏω`): `H (p·gauss) = ℏω · (Mpoly p)·gauss`. -/
noncomputable def Mpoly (p : Polynomial ℝ) : Polynomial ℝ :=
  -(Polynomial.C (hbar / (2 * m * ω)) * derivative (derivative p)) + X * derivative p
    + Polynomial.C (1 / 2) * p

/-- The eigenpolynomials, obtained by applying the raising operator `n` times to `1`. -/
noncomputable def eigenPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | (n + 1) => upPoly m ω hbar (eigenPoly n)

/-- The `n`-th eigenstate of the oscillator. -/
noncomputable def eigenState (n : ℕ) : ℝ → ℝ := stateFun m ω hbar (eigenPoly m ω hbar n)

end Oscillator

end QPhys

namespace QPhys
open Polynomial
section Oscillator
variable (m ω hbar : ℝ)

lemma hasDerivAt_gauss (x : ℝ) :
    HasDerivAt (gauss m ω hbar) (-(m * ω / hbar) * x * gauss m ω hbar x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(m * ω / (2 * hbar)) * y ^ 2)
      (-(m * ω / (2 * hbar)) * (2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul (-(m * ω / (2 * hbar)))
  have h2 := (Real.hasDerivAt_exp (-(m * ω / (2 * hbar)) * x ^ 2)).comp x h1
  have hd : m * ω / (2 * hbar) = (m * ω / hbar) / 2 := by
    rw [show (2 : ℝ) * hbar = hbar * 2 from mul_comm _ _, ← div_div]
  convert h2 using 1
  unfold gauss
  rw [hd]
  ring

lemma hasDerivAt_stateFun (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (stateFun m ω hbar p) (stateFun m ω hbar (Dpoly m ω hbar p) x) x := by
  have hp : HasDerivAt (fun y : ℝ => p.eval y) ((derivative p).eval x) x := p.hasDerivAt x
  have h := hp.mul (hasDerivAt_gauss m ω hbar x)
  convert h using 1
  simp [stateFun, Dpoly]
  ring

lemma deriv_stateFun (p : Polynomial ℝ) :
    deriv (stateFun m ω hbar p) = stateFun m ω hbar (Dpoly m ω hbar p) := by
  funext x
  exact (hasDerivAt_stateFun m ω hbar p x).deriv

lemma hamiltonian_stateFun (hm : m ≠ 0) (hw : ω ≠ 0) (hh : hbar ≠ 0) (p : Polynomial ℝ) :
    hamiltonian m ω hbar (stateFun m ω hbar p)
      = fun x => hbar * ω * stateFun m ω hbar (Mpoly m ω hbar p) x := by
  funext x
  unfold hamiltonian
  rw [deriv_stateFun, deriv_stateFun]
  simp only [stateFun, Dpoly, Mpoly, eval_sub, eval_add, eval_neg, eval_mul, eval_C, eval_X,
    derivative_sub, derivative_mul, derivative_C, derivative_X, zero_mul, one_mul, zero_add,
    add_zero, mul_zero]
  field_simp
  ring

end Oscillator
end QPhys

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

