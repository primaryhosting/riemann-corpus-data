import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real

namespace QPhys

/-- The (unnormalised) stationary states of the infinite square well of width `L`:
`ψ n L x = sin (n π x / L)`. -/
noncomputable def psi (n : ℕ) (L x : ℝ) : ℝ := Real.sin (n * π * x / L)

/-- The energy levels of the infinite square well of width `L` for a particle of mass `m`:
`E n = n² π² ℏ² / (2 m L²)`. -/
noncomputable def energy (m hbar L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * π ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

lemma hasDerivAt_sin_mul (k x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (k * y)) (k * Real.cos (k * x)) x := by
  have h : HasDerivAt (fun y : ℝ => k * y) (k * 1) x := (hasDerivAt_id x).const_mul k
  simpa [mul_comm] using (Real.hasDerivAt_sin (k * x)).comp x h

lemma hasDerivAt_cos_mul (k x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (k * y)) (-(k * Real.sin (k * x))) x := by
  have h : HasDerivAt (fun y : ℝ => k * y) (k * 1) x := (hasDerivAt_id x).const_mul k
  simpa [mul_comm] using (Real.hasDerivAt_cos (k * x)).comp x h

lemma deriv_sin_mul (k : ℝ) :
    deriv (fun y : ℝ => Real.sin (k * y)) = fun x => k * Real.cos (k * x) := by
  funext x
  exact (hasDerivAt_sin_mul k x).deriv

/-- The second derivative of `x ↦ sin (k x)` is `-k² sin (k x)`. -/
lemma deriv2_sin_mul (k x : ℝ) :
    deriv (deriv fun y : ℝ => Real.sin (k * y)) x = -(k ^ 2) * Real.sin (k * x) := by
  rw [deriv_sin_mul k]
  have h : HasDerivAt (fun y : ℝ => k * Real.cos (k * y))
      (k * -(k * Real.sin (k * x))) x := (hasDerivAt_cos_mul k x).const_mul k
  have := h.deriv
  rw [this]; ring

/-- **Particle in a box.**  For a particle of mass `m > 0` in an infinite square well of
width `L > 0`, the state `ψ n (x) = sin (n π x / L)` with `n ≥ 1` satisfies:

* the Dirichlet boundary conditions `ψ n 0 = ψ n L = 0`;
* it is not the zero function;
* the time-independent Schrödinger equation `-ℏ²/(2m) ψ'' = E n ψ` with the
  energy eigenvalue `E n = n² π² ℏ² / (2 m L²)`. -/
theorem particle_in_box (m hbar L : ℝ) (hm : 0 < m) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    psi n L 0 = 0 ∧ psi n L L = 0 ∧ (∃ x, psi n L x ≠ 0) ∧
      ∀ x, -(hbar ^ 2 / (2 * m)) * deriv (deriv (psi n L)) x = energy m hbar L n * psi n L x := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set k : ℝ := (n : ℝ) * π / L with hk
  have hpsi : psi n L = fun y : ℝ => Real.sin (k * y) := by
    funext y; simp [psi, hk]; ring_nf
  refine ⟨?_, ?_, ⟨L / (2 * n), ?_⟩, ?_⟩
  · simp [psi]
  · simp [psi, mul_div_assoc, div_self hL0]
  · have hval : k * (L / (2 * n)) = π / 2 := by
      rw [hk]; field_simp
    show psi n L (L / (2 * n)) ≠ 0
    rw [hpsi]
    show Real.sin (k * (L / (2 * n))) ≠ 0
    rw [hval, Real.sin_pi_div_two]
    norm_num
  · intro x
    rw [hpsi, deriv2_sin_mul k x]
    have hk2 : k ^ 2 = (n : ℝ) ^ 2 * π ^ 2 / L ^ 2 := by
      rw [hk]; field_simp
    rw [energy, hk2]
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

