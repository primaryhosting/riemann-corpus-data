import Mathlib
/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
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

namespace Phys

open MeasureTheory Filter Topology

/-- The auxiliary ("virial current") function
`F x = c * (x * ψ'(x)^2 + ψ(x) * ψ'(x)) - x * (V x - E) * ψ x ^ 2`
attached to a solution of the stationary Schrödinger equation
`-c * ψ'' + V ψ = E ψ` (here `c = ℏ²/2m`). -/
noncomputable def virialCurrent (c E : ℝ) (psi dpsi V : ℝ → ℝ) : ℝ → ℝ :=
  fun x => c * (x * dpsi x ^ 2 + psi x * dpsi x) - x * (V x - E) * psi x ^ 2

/-- **Pointwise virial identity.**  If `psi` solves the stationary Schrödinger equation
`c * psi'' = (V - E) * psi` (i.e. `-c ψ'' + V ψ = E ψ`), then the virial current has
derivative `2 c (ψ')² - x V'(x) ψ(x)²`, i.e. exactly `2·(kinetic density) - (virial density)`. -/
theorem hasDerivAt_virialCurrent (c E : ℝ) (psi dpsi ddpsi V dV : ℝ → ℝ)
    (hpsi : ∀ x, HasDerivAt psi (dpsi x) x)
    (hdpsi : ∀ x, HasDerivAt dpsi (ddpsi x) x)
    (hV : ∀ x, HasDerivAt V (dV x) x)
    (hSch : ∀ x, c * ddpsi x = (V x - E) * psi x) (x : ℝ) :
    HasDerivAt (virialCurrent c E psi dpsi V)
      (2 * c * dpsi x ^ 2 - x * dV x * psi x ^ 2) x := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ => dpsi y ^ 2) (2 * dpsi x * ddpsi x) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hdpsi x).pow 2
  have hpsq : HasDerivAt (fun y : ℝ => psi y ^ 2) (2 * psi x * dpsi x) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (hpsi x).pow 2
  have h1 : HasDerivAt (fun y : ℝ => y * dpsi y ^ 2)
      (1 * dpsi x ^ 2 + x * (2 * dpsi x * ddpsi x)) x := hid.mul hsq
  have h2 : HasDerivAt (fun y : ℝ => psi y * dpsi y)
      (dpsi x * dpsi x + psi x * ddpsi x) x := (hpsi x).mul (hdpsi x)
  have h3 : HasDerivAt (fun y : ℝ => y * (V y - E))
      (1 * (V x - E) + x * dV x) x := hid.mul ((hV x).sub_const E)
  have h4 : HasDerivAt (fun y : ℝ => y * (V y - E) * psi y ^ 2)
      ((1 * (V x - E) + x * dV x) * psi x ^ 2
        + x * (V x - E) * (2 * psi x * dpsi x)) x := h3.mul hpsq
  have h5 := ((h1.add h2).const_mul c).sub h4
  simpa only [virialCurrent] using h5.congr_deriv (by
    linear_combination (2 * x * dpsi x + psi x) * hSch x)

/-- **Quantum virial theorem (one dimension).**

Let `psi : ℝ → ℝ` be a (real) bound stationary state of the Schrödinger operator
`H = -(ℏ²/2m) d²/dx² + V`, i.e. `psi` is twice differentiable with derivatives
`dpsi`, `ddpsi` and satisfies `-(ℏ²/2m) * ddpsi + V * psi = E * psi`.
Assume the potential `V` is differentiable with derivative `dV`, that the kinetic
and virial densities are integrable, and that the state is *bound*, in the sense
that the boundary quantities `x·ψ'(x)²`, `ψ(x)·ψ'(x)` and `x·(V x - E)·ψ(x)²`
all vanish at `±∞`.

Then `2⟨T⟩ = ⟨x·V'(x)⟩` (in one dimension `r·∇V = x V'(x)`), where
`⟨T⟩ = ∫ (ℏ²/2m) ψ'(x)² dx` is the expected kinetic energy and
`⟨x V'⟩ = ∫ x V'(x) ψ(x)² dx`.

No normalization of `psi` is needed: the identity holds verbatim for any
solution satisfying the stated decay and integrability assumptions (for a
normalized state, `∫ ψ² = 1`, the two sides are literally `2⟨T⟩` and `⟨r·∇V⟩`).

The proof is the integrated form of the pointwise identity
`(ℏ²/2m · (x ψ'² + ψψ') - x (V - E) ψ²)' = 2 (ℏ²/2m) ψ'² - x V' ψ²`
(`Phys.hasDerivAt_virialCurrent`) combined with the fundamental theorem of calculus
on the whole line, `MeasureTheory.integral_of_hasDerivAt_of_tendsto`. -/
theorem virial_theorem (hbar mass E : ℝ) (psi dpsi ddpsi V dV : ℝ → ℝ)
    (hpsi : ∀ x, HasDerivAt psi (dpsi x) x)
    (hdpsi : ∀ x, HasDerivAt dpsi (ddpsi x) x)
    (hV : ∀ x, HasDerivAt V (dV x) x)
    -- stationary Schrödinger equation `H ψ = E ψ`
    (hSch : ∀ x, -(hbar ^ 2 / (2 * mass)) * ddpsi x + V x * psi x = E * psi x)
    -- integrability of the kinetic and virial densities
    (hT : Integrable (fun x => dpsi x ^ 2) volume)
    (hW : Integrable (fun x => x * dV x * psi x ^ 2) volume)
    -- boundary terms vanish (the state is bound)
    (hb1 : Tendsto (fun x => x * dpsi x ^ 2) atBot (𝓝 0))
    (hb2 : Tendsto (fun x => x * dpsi x ^ 2) atTop (𝓝 0))
    (hb3 : Tendsto (fun x => psi x * dpsi x) atBot (𝓝 0))
    (hb4 : Tendsto (fun x => psi x * dpsi x) atTop (𝓝 0))
    (hb5 : Tendsto (fun x => x * (V x - E) * psi x ^ 2) atBot (𝓝 0))
    (hb6 : Tendsto (fun x => x * (V x - E) * psi x ^ 2) atTop (𝓝 0)) :
    2 * ∫ x, (hbar ^ 2 / (2 * mass)) * dpsi x ^ 2
      = ∫ x, x * dV x * psi x ^ 2 := by
  set c : ℝ := hbar ^ 2 / (2 * mass)
  have hSch' : ∀ x, c * ddpsi x = (V x - E) * psi x := fun x => by linarith [hSch x]
  have hderiv := hasDerivAt_virialCurrent c E psi dpsi ddpsi V dV hpsi hdpsi hV hSch'
  have hint : Integrable (fun x => 2 * c * dpsi x ^ 2 - x * dV x * psi x ^ 2) volume :=
    (hT.const_mul (2 * c)).sub hW
  have hlim_bot : Tendsto (virialCurrent c E psi dpsi V) atBot (𝓝 0) := by
    have : Tendsto (fun x => c * (x * dpsi x ^ 2 + psi x * dpsi x)
        - x * (V x - E) * psi x ^ 2) atBot (𝓝 (c * (0 + 0) - 0)) :=
      ((hb1.add hb3).const_mul c).sub hb5
    simpa [virialCurrent] using this
  have hlim_top : Tendsto (virialCurrent c E psi dpsi V) atTop (𝓝 0) := by
    have : Tendsto (fun x => c * (x * dpsi x ^ 2 + psi x * dpsi x)
        - x * (V x - E) * psi x ^ 2) atTop (𝓝 (c * (0 + 0) - 0)) :=
      ((hb2.add hb4).const_mul c).sub hb6
    simpa [virialCurrent] using this
  have key : ∫ x, (2 * c * dpsi x ^ 2 - x * dV x * psi x ^ 2) = 0 := by
    simpa using
      MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hint hlim_bot hlim_top
  rw [integral_sub (hT.const_mul (2 * c)) hW] at key
  have hTc : ∫ x, c * dpsi x ^ 2 = c * ∫ x, dpsi x ^ 2 := integral_const_mul c _
  have h2c : ∫ x, 2 * c * dpsi x ^ 2 = 2 * c * ∫ x, dpsi x ^ 2 := by
    simpa [mul_assoc] using integral_const_mul (2 * c) (fun x => dpsi x ^ 2)
  rw [h2c] at key
  rw [hTc]
  linarith

/-! ### Non-vacuity: the harmonic-oscillator ground state satisfies all the hypotheses -/

/-- `x ^ n * exp (-x²) → 0` as `x → +∞`. -/
theorem tendsto_pow_mul_gaussian_atTop (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t ^ n * Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  refine squeeze_zero' ?_ ?_ (h.comp hsq)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx; positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by nlinarith) n)
      (Real.exp_nonneg _)

/-- `x ^ n * exp (-x²) → 0` as `x → -∞`. -/
theorem tendsto_pow_mul_gaussian_atBot (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := ((tendsto_pow_mul_gaussian_atTop n).comp tendsto_neg_atBot_atTop).const_mul ((-1:ℝ) ^ n)
  rw [mul_zero] at h
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, neg_sq]
  have hone : ((-1:ℝ) ^ n) * ((-1:ℝ) ^ n) = 1 := by rw [← mul_pow]; norm_num
  have h2 : (-x:ℝ) ^ n = (-1) ^ n * x ^ n := by rw [← neg_one_mul, mul_pow]
  rw [h2]
  calc (-1:ℝ) ^ n * ((-1) ^ n * x ^ n * Real.exp (-x ^ 2))
      = ((-1:ℝ) ^ n * (-1) ^ n) * (x ^ n * Real.exp (-x ^ 2)) := by ring
    _ = x ^ n * Real.exp (-x ^ 2) := by rw [hone, one_mul]

/-- `x ↦ x² exp (-x²)` is integrable on `ℝ`. -/
theorem integrable_sq_mul_gaussian :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2)) volume := by
  have hg : Integrable (fun x : ℝ => 2 * Real.exp (-(1/2 : ℝ) * x ^ 2)) volume :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul 2
  refine Integrable.mono' hg
    ((continuous_pow 2).mul
      (Real.continuous_exp.comp (continuous_pow 2).neg)).aestronglyMeasurable ?_
  filter_upwards with x
  have h1 : x ^ 2 / 2 + 1 ≤ Real.exp (x ^ 2 / 2) := Real.add_one_le_exp _
  have hpos : (0:ℝ) < Real.exp (x ^ 2 / 2) := Real.exp_pos _
  have hApos : (0:ℝ) < Real.exp (-(1/2:ℝ) * x ^ 2) := Real.exp_pos _
  have hx : Real.exp (-x ^ 2) = Real.exp (-(1/2:ℝ) * x ^ 2) / Real.exp (x ^ 2 / 2) := by
    rw [eq_div_iff (ne_of_gt hpos), ← Real.exp_add]; ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hx, mul_div_assoc', div_le_iff₀ hpos]
  nlinarith [hApos, h1, sq_nonneg x]

/-- `exp (-x²/2) ^ 2 = exp (-x²)`. -/
theorem gaussian_sq (x : ℝ) : Real.exp (-x ^ 2 / 2) ^ 2 = Real.exp (-x ^ 2) := by
  rw [sq, ← Real.exp_add]; ring_nf

/-- **The hypotheses of `Phys.virial_theorem` are not vacuous.**  The ground state
`ψ(x) = exp (-x²/2)` of the harmonic oscillator (`ℏ = m = 1`, `V x = x²/2`, `E = 1/2`)
is a nowhere-vanishing bound stationary state satisfying every assumption of the theorem. -/
theorem virial_hypotheses_satisfiable :
    ∃ (psi dpsi ddpsi V dV : ℝ → ℝ) (E : ℝ),
      (∀ x, psi x ≠ 0) ∧
      (∀ x, HasDerivAt psi (dpsi x) x) ∧
      (∀ x, HasDerivAt dpsi (ddpsi x) x) ∧
      (∀ x, HasDerivAt V (dV x) x) ∧
      (∀ x, -((1:ℝ) ^ 2 / (2 * 1)) * ddpsi x + V x * psi x = E * psi x) ∧
      Integrable (fun x => dpsi x ^ 2) volume ∧
      Integrable (fun x => x * dV x * psi x ^ 2) volume ∧
      Tendsto (fun x => x * dpsi x ^ 2) atBot (𝓝 0) ∧
      Tendsto (fun x => x * dpsi x ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun x => psi x * dpsi x) atBot (𝓝 0) ∧
      Tendsto (fun x => psi x * dpsi x) atTop (𝓝 0) ∧
      Tendsto (fun x => x * (V x - E) * psi x ^ 2) atBot (𝓝 0) ∧
      Tendsto (fun x => x * (V x - E) * psi x ^ 2) atTop (𝓝 0) := by
  have hinner : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := fun x =>
    ((hasDerivAt_pow 2 x).neg.div_const 2).congr_deriv (by push_cast; ring)
  have hpsi : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2)) (-x * Real.exp (-x ^ 2 / 2)) x := fun x =>
    (hinner x).exp.congr_deriv (by ring)
  have hcube : (fun x : ℝ => x * (-x * Real.exp (-x ^ 2 / 2)) ^ 2)
      = fun x : ℝ => x ^ 3 * Real.exp (-x ^ 2) := by
    funext x; rw [mul_pow, gaussian_sq]; ring
  have hlin : (fun x : ℝ => Real.exp (-x ^ 2 / 2) * (-x * Real.exp (-x ^ 2 / 2)))
      = fun x : ℝ => -(x ^ 1 * Real.exp (-x ^ 2)) := by
    funext x
    have h : Real.exp (-x ^ 2 / 2) * (-x * Real.exp (-x ^ 2 / 2))
        = -(x * Real.exp (-x ^ 2 / 2) ^ 2) := by ring
    rw [h, gaussian_sq]; ring
  have hvir : (fun x : ℝ => x * (x ^ 2 / 2 - 1/2) * Real.exp (-x ^ 2 / 2) ^ 2)
      = fun x : ℝ => (1/2 : ℝ) * (x ^ 3 * Real.exp (-x ^ 2))
          - (1/2 : ℝ) * (x ^ 1 * Real.exp (-x ^ 2)) := by
    funext x; rw [gaussian_sq]; ring
  refine ⟨fun x => Real.exp (-x ^ 2 / 2), fun x => -x * Real.exp (-x ^ 2 / 2),
    fun x => (x ^ 2 - 1) * Real.exp (-x ^ 2 / 2), fun x => x ^ 2 / 2, fun x => x, 1/2,
    fun x => Real.exp_ne_zero _, hpsi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hn : HasDerivAt (fun y : ℝ => -y) (-1:ℝ) x := by simpa using (hasDerivAt_id x).neg
    exact (hn.mul (hpsi x)).congr_deriv (by ring)
  · intro x
    exact ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by push_cast; ring)
  · intro x; ring
  · have h : (fun x : ℝ => (-x * Real.exp (-x ^ 2 / 2)) ^ 2)
        = fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) := by
      funext x; rw [mul_pow, gaussian_sq]; ring
    rw [h]; exact integrable_sq_mul_gaussian
  · have h : (fun x : ℝ => x * x * Real.exp (-x ^ 2 / 2) ^ 2)
        = fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) := by
      funext x; rw [gaussian_sq]; ring
    rw [h]; exact integrable_sq_mul_gaussian
  · rw [hcube]; exact tendsto_pow_mul_gaussian_atBot 3
  · rw [hcube]; exact tendsto_pow_mul_gaussian_atTop 3
  · rw [hlin]; simpa using (tendsto_pow_mul_gaussian_atBot 1).neg
  · rw [hlin]; simpa using (tendsto_pow_mul_gaussian_atTop 1).neg
  · have h := ((tendsto_pow_mul_gaussian_atBot 3).const_mul (1/2 : ℝ)).sub
      ((tendsto_pow_mul_gaussian_atBot 1).const_mul (1/2 : ℝ))
    rw [mul_zero, sub_zero] at h
    rw [hvir]; exact h
  · have h := ((tendsto_pow_mul_gaussian_atTop 3).const_mul (1/2 : ℝ)).sub
      ((tendsto_pow_mul_gaussian_atTop 1).const_mul (1/2 : ℝ))
    rw [mul_zero, sub_zero] at h
    rw [hvir]; exact h

end Phys

