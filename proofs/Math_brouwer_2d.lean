import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The proof follows the classical winding-number argument.

If `f` is a continuous self-map of the closed unit disk `D ⊆ ℂ` with no fixed point, then
`u z = z - f z` is a continuous nowhere-vanishing function on `D`.  Since `D` is convex, it is
contractible, hence simply connected and locally path connected, so `u` admits a continuous
logarithm `L : D → ℂ`, i.e. `exp (L z) = z - f z`.

Restricting to the boundary circle `t ↦ exp (t * I)` and setting `ψ t = (L (exp (t*I))).im - t`,
one checks that `cos (ψ t) ≥ 0` for all `t` (because `Re ((z - f z) * conj z) ≥ 1 - ‖f z‖ ≥ 0`),
while `ψ (2π) = ψ 0 - 2π`.  The intermediate value theorem then forces `ψ` to hit a point of
`π + 2πℤ`, where the cosine is `-1`: a contradiction.
-/

namespace Math

open Complex Metric Set

/-- A continuous nowhere-vanishing complex-valued function on a simply connected, locally
path-connected space admits a continuous logarithm. -/
theorem exists_continuous_complex_log {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocPathConnectedSpace A] [Nonempty A] (u : A → ℂ) (hu : Continuous u) (h0 : ∀ a, u a ≠ 0) :
    ∃ L : A → ℂ, Continuous L ∧ ∀ a, Complex.exp (L a) = u a := by
  classical
  set p : ℂ → {z : ℂ // z ≠ 0} := fun z ↦ ⟨Complex.exp z, z.exp_ne_zero⟩ with hp
  have cov : IsCoveringMap p := Complex.isCoveringMap_exp
  set û : C(A, {z : ℂ // z ≠ 0}) :=
    ⟨fun a ↦ ⟨u a, h0 a⟩, by fun_prop⟩ with hû
  obtain ⟨a₀⟩ := ‹Nonempty A›
  have he : p (Complex.log (u a₀)) = û a₀ := by
    apply Subtype.ext
    simpa [hp, hû] using Complex.exp_log (h0 a₀)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := cov.existsUnique_continuousMap_lifts û a₀ (Complex.log (u a₀)) he
  refine ⟨F, F.continuous, fun a ↦ ?_⟩
  have := congrArg (fun g ↦ (g a : {z : ℂ // z ≠ 0})) hF
  simpa [hp, hû] using congrArg Subtype.val this

/-- Auxiliary: on the unit circle, `Re ((z - w) * exp (-t*I)) ≥ 0` whenever `z = exp (t*I)`
and `‖w‖ ≤ 1`. -/
theorem re_sub_mul_nonneg (t : ℝ) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    0 ≤ ((Complex.exp (t * I) - w) * Complex.exp (-(t * I))).re := by
  have hmul : (Complex.exp (t * I) - w) * Complex.exp (-(t * I))
      = 1 - w * Complex.exp (-(t * I)) := by
    rw [sub_mul, ← Complex.exp_add]
    simp
  rw [hmul]
  have h1 : ‖w * Complex.exp (-(t * I))‖ ≤ 1 := by
    rw [norm_mul]
    have : ‖Complex.exp (-((t : ℂ) * I))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [this, mul_one]
    exact hw
  have h2 : (w * Complex.exp (-(t * I))).re ≤ ‖w * Complex.exp (-(t * I))‖ :=
    Complex.re_le_norm _
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- Any closed interval of length `2π` contains a point of `π + 2πℤ`. -/
theorem exists_odd_multiple_pi_mem_Icc (a : ℝ) :
    ∃ c : ℝ, c ∈ Set.Icc (a - 2 * Real.pi) a ∧ Real.cos c = -1 := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  set k : ℤ := ⌊(a - Real.pi) / (2 * Real.pi)⌋ with hk
  refine ⟨Real.pi + k * (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · have : ((a - Real.pi) / (2 * Real.pi)) < k + 1 := Int.lt_floor_add_one _
    have := (div_lt_iff₀ hpi).1 this
    nlinarith
  · have : (k : ℝ) ≤ (a - Real.pi) / (2 * Real.pi) := Int.floor_le _
    have := (le_div_iff₀ hpi).1 this
    linarith
  · rw [Real.cos_add_int_mul_two_pi, Real.cos_pi]

/-- **Brouwer's fixed point theorem in dimension 2.**
Every continuous self-map of the closed unit disk in `ℂ ≅ ℝ²` has a fixed point. -/
theorem brouwer_2d (f : ℂ → ℂ) (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo f (Metric.closedBall (0 : ℂ) 1) (Metric.closedBall 0 1)) :
    ∃ z ∈ Metric.closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  set D : Set ℂ := Metric.closedBall (0 : ℂ) 1 with hD
  have hDconv : Convex ℝ D := convex_closedBall _ _
  have hDne : (0 : ℂ) ∈ D := by simp [hD]
  haveI : Nonempty D := ⟨⟨0, hDne⟩⟩
  haveI : ContractibleSpace D := hDconv.contractibleSpace ⟨⟨0, hDne⟩⟩
  haveI : LocPathConnectedSpace D := hDconv.locPathConnectedSpace
  -- the continuous nowhere-vanishing map `z ↦ z - f z`
  have hfc : Continuous (D.restrict f) := continuousOn_iff_continuous_restrict.1 hf
  set u : D → ℂ := fun z ↦ (z : ℂ) - f z with hu
  have huc : Continuous u := by
    exact continuous_subtype_val.sub hfc
  have hu0 : ∀ z : D, u z ≠ 0 := by
    intro z hz
    exact hcon z z.2 (by rw [hu] at hz; simpa [sub_eq_zero, eq_comm] using hz)
  obtain ⟨L, hLc, hL⟩ := exists_continuous_complex_log u huc hu0
  -- the boundary parametrization
  have hmem : ∀ t : ℝ, Complex.exp ((t : ℂ) * I) ∈ D := by
    intro t
    simp [hD, mem_closedBall_zero_iff, Complex.norm_exp]
  set P : ℝ → D := fun t ↦ ⟨Complex.exp ((t : ℂ) * I), hmem t⟩ with hP
  have hPc : Continuous P := by
    apply Continuous.subtype_mk
    fun_prop
  set ψ : ℝ → ℝ := fun t ↦ (L (P t)).im - t with hψ
  have hψc : Continuous ψ := by
    exact ((Complex.continuous_im.comp (hLc.comp hPc)).sub continuous_id)
  -- `cos (ψ t) ≥ 0`
  have hcos : ∀ t : ℝ, 0 ≤ Real.cos (ψ t) := by
    intro t
    have hw : ‖f (Complex.exp ((t : ℂ) * I))‖ ≤ 1 := by
      have := hmaps (hmem t)
      simpa [hD, mem_closedBall_zero_iff] using this
    have key := re_sub_mul_nonneg t (f (Complex.exp ((t : ℂ) * I))) hw
    have hval : (Complex.exp ((t : ℂ) * I) - f (Complex.exp ((t : ℂ) * I)))
        * Complex.exp (-((t : ℂ) * I)) = Complex.exp (L (P t) - (t : ℂ) * I) := by
      rw [Complex.exp_sub]
      have : Complex.exp (L (P t)) = Complex.exp ((t : ℂ) * I) - f (Complex.exp ((t : ℂ) * I)) := by
        have := hL (P t)
        simpa [hu, hP] using this
      rw [this, ← Complex.exp_neg]
      ring_nf
      rw [← Complex.exp_add]
      ring_nf
    rw [hval] at key
    rw [Complex.exp_re] at key
    have hpos : 0 < Real.exp ((L (P t) - (t : ℂ) * I).re) := Real.exp_pos _
    have him : (L (P t) - (t : ℂ) * I).im = ψ t := by
      simp [hψ]
    rw [him] at key
    nlinarith
  -- `ψ (2π) = ψ 0 - 2π`
  have hP0 : P (2 * Real.pi) = P 0 := by
    apply Subtype.ext
    simp [hP, Complex.exp_two_pi_mul_I]
  have hψ2 : ψ (2 * Real.pi) = ψ 0 - 2 * Real.pi := by
    simp [hψ, hP0]
  -- IVT
  obtain ⟨c, hcmem, hcc⟩ := exists_odd_multiple_pi_mem_Icc (ψ 0)
  have hsub : Set.Icc (ψ (2 * Real.pi)) (ψ 0) ⊆ ψ '' Set.Icc 0 (2 * Real.pi) :=
    intermediate_value_Icc' (by positivity) hψc.continuousOn
  have : c ∈ Set.Icc (ψ (2 * Real.pi)) (ψ 0) := by rw [hψ2]; exact hcmem
  obtain ⟨t, -, ht⟩ := hsub this
  have := hcos t
  rw [ht, hcc] at this
  linarith

end Math

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

