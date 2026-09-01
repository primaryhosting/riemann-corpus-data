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

import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RiemannScaffold

open Complex

/-- The Riemann Hypothesis, in the form: every zero of `riemannZeta` lying in the
right half-plane `0 < Re s` lies on the critical line `Re s = 1 / 2`.

(Since `riemannZeta` has no zeros with `Re s ≥ 1`, this is the usual statement that
every nontrivial zero lies on the critical line.) -/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ, 0 < s.re → riemannZeta s = 0 → s.re = 1 / 2

/-- A **Brockian system** for the Riemann zeta function: a function `brockLog` which
exponentiates to `riemannZeta` on the right half `{1/2 < Re s < 1}` of the critical
strip, i.e. a (not necessarily continuous) choice of logarithm of `ζ` there. -/
structure BrockianSystem where
  /-- The Brockian logarithm attached to the system. -/
  brockLog : ℂ → ℂ
  /-- `brockLog` is a logarithm of `riemannZeta` on the right half of the critical strip. -/
  exp_brockLog : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → Complex.exp (brockLog s) = riemannZeta s

namespace BrockianSystem

/-- A Brockian system forces `riemannZeta` to be nonvanishing on the right half of the
critical strip, since the complex exponential is nowhere zero. -/
theorem zeta_ne_zero (B : BrockianSystem) {s : ℂ} (h1 : 1 / 2 < s.re) (h2 : s.re < 1) :
    riemannZeta s ≠ 0 := by
  rw [← B.exp_brockLog s h1 h2]
  exact Complex.exp_ne_zero _

end BrockianSystem

/-- **The Riemann Hypothesis holds for any Brockian system.**

Given a Brockian system (a logarithm of `ζ` on the right half of the critical strip),
every zero of `riemannZeta` with positive real part lies on the critical line.

The three regimes are handled separately: `Re s ≥ 1` by the classical nonvanishing of `ζ`
there, `1/2 < Re s < 1` by the Brockian system itself, and `0 < Re s < 1/2` by reflecting
through the functional equation. -/
theorem RH_of_BrockianSystem (B : BrockianSystem) : RiemannHypothesis := by
  intro s hs hz
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · -- Reflect: `ζ (1 - s) = 0` too, and `1 - s` lies in the right half of the strip.
    exfalso
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hlt
      norm_num at hlt
    have hsn : ∀ n : ℕ, s ≠ -(n : ℂ) := by
      intro n h
      have hre : s.re = -(n : ℝ) := by rw [h]; simp
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hre] at hs
      linarith
    have hone : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_one_sub hsn hs1, hz, mul_zero]
    have hre : ((1 : ℂ) - s).re = 1 - s.re := by simp
    exact B.zeta_ne_zero (s := 1 - s) (by rw [hre]; linarith) (by rw [hre]; linarith) hone
  · exact heq
  · exfalso
    rcases lt_or_ge s.re 1 with h1 | h1
    · exact B.zeta_ne_zero hgt h1 hz
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz

/-- Conversely, the Riemann Hypothesis produces a Brockian system: the principal
logarithm of `ζ` works. -/
noncomputable def brockianSystemOfRH (h : RiemannHypothesis) : BrockianSystem where
  brockLog := fun s => Complex.log (riemannZeta s)
  exp_brockLog := by
    intro s h1 h2
    refine Complex.exp_log (fun hz => ?_)
    have := h s (by linarith) hz
    linarith

/-- The existence of a Brockian system is *equivalent* to the Riemann Hypothesis; in
particular the hypothesis discharged in `RH_of_BrockianSystem` is not vacuous. -/
theorem nonempty_brockianSystem_iff : Nonempty BrockianSystem ↔ RiemannHypothesis :=
  ⟨fun ⟨B⟩ => RH_of_BrockianSystem B, fun h => ⟨brockianSystemOfRH h⟩⟩

end RiemannScaffold
end Brockian

