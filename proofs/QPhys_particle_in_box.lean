/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

/-- The (unnormalized) stationary state of a particle in an infinite square well
of width `L`: `ψ_n(x) = sin (n π x / L)`. -/
noncomputable def boxWave (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n * Real.pi / L) * x)

/-- The energy levels of a particle of mass `m` in an infinite square well of width `L`:
`E_n = n² π² ℏ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

lemma hasDerivAt_boxWave (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (boxWave L n) (Real.cos ((n * Real.pi / L) * x) * ((n : ℝ) * Real.pi / L)) x := by
  have h : HasDerivAt (fun x : ℝ => ((n : ℝ) * Real.pi / L) * x)
      ((n : ℝ) * Real.pi / L) x := by
    simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi / L)
  simpa [boxWave] using (Real.hasDerivAt_sin _).comp x h

lemma deriv_boxWave (L : ℝ) (n : ℕ) :
    deriv (boxWave L n) = fun x => Real.cos ((n * Real.pi / L) * x) * ((n : ℝ) * Real.pi / L) := by
  funext x
  exact (hasDerivAt_boxWave L n x).deriv

lemma deriv2_boxWave (L : ℝ) (n : ℕ) (x : ℝ) :
    deriv (deriv (boxWave L n)) x = -((n : ℝ) * Real.pi / L) ^ 2 * boxWave L n x := by
  rw [deriv_boxWave]
  have h : HasDerivAt (fun x : ℝ => ((n : ℝ) * Real.pi / L) * x)
      ((n : ℝ) * Real.pi / L) x := by
    simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi / L)
  have hc : HasDerivAt (fun x : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * x))
      (-Real.sin (((n : ℝ) * Real.pi / L) * x) * ((n : ℝ) * Real.pi / L)) x :=
    (Real.hasDerivAt_cos _).comp x h
  have := (hc.mul_const ((n : ℝ) * Real.pi / L)).deriv
  rw [this]
  simp [boxWave]
  ring

/--
**Particle in a one-dimensional infinite square well of width `L`.**

For a particle of mass `m > 0` in a box `[0, L]` with `L > 0`, and for each `n ≥ 1`,
the function `ψ_n(x) = sin (n π x / L)` is a nontrivial solution of the time-independent
Schrödinger equation `-(ℏ²/2m) ψ'' = E ψ` satisfying the hard-wall boundary conditions
`ψ(0) = ψ(L) = 0`, with energy eigenvalue

`E_n = n² π² ℏ² / (2 m L²)`.
-/
theorem particle_in_box (hbar m L : ℝ) (hm : 0 < m) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    boxWave L n 0 = 0 ∧ boxWave L n L = 0 ∧
    (∃ x, boxWave L n x ≠ 0) ∧
    ∀ x, -(hbar ^ 2 / (2 * m)) * deriv (deriv (boxWave L n)) x
        = boxEnergy hbar m L n * boxWave L n x := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨by simp [boxWave], ?_, ⟨L / (2 * n), ?_⟩, ?_⟩
  · have : (n : ℝ) * Real.pi / L * L = n * Real.pi := by field_simp
    rw [boxWave, this, Real.sin_nat_mul_pi]
  · have : (n : ℝ) * Real.pi / L * (L / (2 * n)) = Real.pi / 2 := by
      field_simp
    rw [boxWave, this, Real.sin_pi_div_two]
    exact one_ne_zero
  · intro x
    rw [deriv2_boxWave, boxEnergy]
    have hm' : m ≠ 0 := ne_of_gt hm
    field_simp

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

