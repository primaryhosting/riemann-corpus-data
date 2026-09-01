/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate

namespace QPhys

section Strong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- On a finite-dimensional space, strong continuity of a family of operators implies
continuity in the operator norm. -/
theorem continuous_of_strongly_continuous (U : ℝ → (E →L[ℂ] E))
    (hstrong : ∀ x, Continuous fun t => U t x) : Continuous U := by
  classical
  set b := Module.finBasis ℂ E with hb
  set Ψ : (Fin (Module.finrank ℂ E) → E) ≃ₗ[ℂ] (E →L[ℂ] E) :=
    (b.constr ℂ).trans LinearMap.toContinuousLinearMap with hΨ
  have hΨcont : Continuous Ψ :=
    LinearMap.continuous_of_finiteDimensional (Ψ : (Fin (Module.finrank ℂ E) → E) →ₗ[ℂ] (E →L[ℂ] E))
  have hUeq : U = fun t => Ψ (fun i => U t (b i)) := by
    funext t
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    simp [hΨ]
  rw [hUeq]
  exact hΨcont.comp (continuous_pi fun i => hstrong (b i))

end Strong

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A norm-continuous one-parameter group in a Banach algebra has a bounded generator `B`:
`U` is differentiable and `U' t = U t * B`.

The generator is produced by the classical averaging trick: for small `s > 0` the element
`V s = ∫ t in 0..s, U t` is invertible (it is close to `s • 1`), and the group law turns
`U r` into `(V (r + s) - V r) * (V s)⁻¹`, which is differentiable in `r`. -/
theorem exists_generator_of_continuous (U : ℝ → A)
    (hgroup : ∀ s t, U (s + t) = U s * U t) (hone : U 0 = 1) (hcont : Continuous U) :
    ∃ B : A, ∀ t, HasDerivAt U (U t * B) t := by
  have hint : ∀ a b : ℝ, IntervalIntegrable U MeasureTheory.volume a b := fun a b =>
    hcont.intervalIntegrable a b
  set V : ℝ → A := fun r => ∫ t in (0:ℝ)..r, U t with hVdef
  have hV' : ∀ r, HasDerivAt V (U r) r := fun r =>
    intervalIntegral.integral_hasDerivAt_right (hint 0 r)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  -- pick `s > 0` on which `U` stays close to the identity
  obtain ⟨s, hs0, hsle⟩ : ∃ s : ℝ, 0 < s ∧ ∀ t ∈ Set.uIoc (0:ℝ) s, ‖U t - 1‖ ≤ 1/2 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := 0)) (1/2)
      (by norm_num)
    refine ⟨δ/2, by linarith, ?_⟩
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      linarith [ht.2]
    have := (h hdist).le
    simpa [hone, dist_eq_norm] using this
  have hne : s ≠ 0 := ne_of_gt hs0
  have hVs : ‖V s - s • (1 : A)‖ ≤ (1/2) * s := by
    have hsub : V s - s • (1 : A) = ∫ t in (0:ℝ)..s, (U t - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 s) intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp [hVdef]
    rw [hsub]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1/2) (f := fun t => U t - 1) (a := 0) (b := s) hsle
    simpa [abs_of_pos hs0] using this
  have h1a : ‖(1 : A) - s⁻¹ • V s‖ < 1 := by
    have heq : (1 : A) - s⁻¹ • V s = s⁻¹ • (s • (1 : A) - V s) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [heq, norm_smul]
    have hnorm : ‖s • (1 : A) - V s‖ ≤ 1/2 * s := by
      rw [← norm_neg]
      simpa [neg_sub] using hVs
    have hpos : ‖(s⁻¹ : ℝ)‖ = s⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs0)]
    rw [hpos]
    calc s⁻¹ * ‖s • (1 : A) - V s‖ ≤ s⁻¹ * (1/2 * s) :=
          mul_le_mul_of_nonneg_left hnorm (le_of_lt (inv_pos.2 hs0))
      _ = 1/2 := by field_simp
      _ < 1 := by norm_num
  set u : Aˣ := Units.oneSub ((1 : A) - s⁻¹ • V s) h1a with hudef
  have hu : (u : A) = s⁻¹ • V s := by simp [hudef, Units.oneSub]
  set W : A := s⁻¹ • ((u⁻¹ : Aˣ) : A) with hWdef
  have hVsa : V s = s • (s⁻¹ • V s) := by rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hVW : V s * W = 1 := by
    rw [hVsa, hWdef, smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hne, one_smul,
      ← hu, u.mul_inv]
  have hkey : ∀ r, U r * V s = V (r + s) - V r := by
    intro r
    have h1 : U r * V s = ∫ t in (0:ℝ)..s, U r * U t :=
      ((ContinuousLinearMap.mul ℝ A (U r)).intervalIntegral_comp_comm (hint 0 s)).symm
    have h2 : (∫ t in (0:ℝ)..s, U r * U t) = ∫ t in (0:ℝ)..s, U (r + t) := by
      simp only [hgroup]
    have h3 : (∫ t in (0:ℝ)..s, U (r + t)) = ∫ t in (r + 0)..(r + s), U t :=
      intervalIntegral.integral_comp_add_left U r
    have h4 : V (r + s) - V r = ∫ t in r..(r + s), U t :=
      intervalIntegral.integral_interval_sub_left (hint 0 (r + s)) (hint 0 r)
    rw [h1, h2, h3, h4, add_zero]
  refine ⟨(U s - 1) * W, ?_⟩
  intro r
  have hUeq : ∀ r, U r = (V (r + s) - V r) * W := by
    intro r
    rw [← hkey r, mul_assoc, hVW, mul_one]
  have hd : HasDerivAt (fun r => (V (r + s) - V r) * W) ((U (r + s) - U r) * W) r :=
    ((HasDerivAt.comp_add_const r s (hV' (r + s))).sub (hV' r)).mul_const W
  have hd2 : HasDerivAt U ((U (r + s) - U r) * W) r :=
    hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hUeq)
  have hval : (U (r + s) - U r) * W = U r * ((U s - 1) * W) := by
    rw [hgroup r s]
    noncomm_ring
  rwa [hval] at hd2

/-- The generator commutes with the group: `U t * B = B * U t`. -/
theorem generator_comm (U : ℝ → A) (B : A) (hgroup : ∀ s t, U (s + t) = U s * U t)
    (hone : U 0 = 1) (hB : ∀ t, HasDerivAt U (U t * B) t) (t : ℝ) : U t * B = B * U t := by
  have h1 : HasDerivAt (fun r => U (t + r)) (U t * B) 0 := by
    have := (hB 0).const_mul (U t)
    rw [hone, one_mul] at this
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => hgroup t r)
  have h2 : HasDerivAt (fun r => U (t + r)) (B * U t) 0 := by
    have := (hB 0).mul_const (U t)
    rw [hone, one_mul] at this
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    rw [add_comm t r, hgroup r t]
  exact h1.unique h2

end BanachAlgebra

section Generator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- If a one-parameter unitary group has derivative `B` at `0` (in the strong sense),
then `B` is skew-adjoint. -/
theorem star_eq_neg_of_unitary (U : ℝ → (E →L[ℂ] E)) (B : E →L[ℂ] E) (hone : U 0 = 1)
    (hunitary : ∀ t x y, inner ℂ (U t x) (U t y) = (inner ℂ x y : ℂ))
    (hB : ∀ x, HasDerivAt (fun t => U t x) (B x) 0) : star B = -B := by
  have key : ∀ x y : E, (inner ℂ x (B y) : ℂ) + inner ℂ (B x) y = 0 := by
    intro x y
    have hd : HasDerivAt (fun t => (inner ℂ (U t x) (U t y) : ℂ))
        (inner ℂ (U 0 x) (B y) + inner ℂ (B x) (U 0 y)) 0 := (hB x).inner ℂ (hB y)
    have hconst : HasDerivAt (fun t : ℝ => (inner ℂ (U t x) (U t y) : ℂ)) 0 0 := by
      simp only [hunitary]
      exact hasDerivAt_const _ _
    have h0 := hd.unique hconst
    simpa [hone] using h0
  ext x
  refine ext_inner_right ℂ ?_
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have := key x y
  simp only [ContinuousLinearMap.neg_apply, inner_neg_left]
  linear_combination (norm := module) this

end Generator

/-- **Stone's theorem** (bounded / finite-dimensional case).

A strongly continuous one-parameter unitary group `U` on a finite-dimensional complex
Hilbert space has a self-adjoint generator `H`: for every state `x` the orbit `t ↦ U t x`
solves the Schrödinger equation `d/dt (U t x) = -i • H (U t x)`, and `H` commutes with
the group. -/
theorem stone_generator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] (U : ℝ → (E →L[ℂ] E))
    (hgroup : ∀ s t, U (s + t) = U s * U t) (hone : U 0 = 1)
    (hunitary : ∀ t x y, inner ℂ (U t x) (U t y) = (inner ℂ x y : ℂ))
    (hstrong : ∀ x, Continuous fun t => U t x) :
    ∃ H : E →L[ℂ] E, IsSelfAdjoint H ∧
      (∀ t x, HasDerivAt (fun r => U r x) (-Complex.I • H (U t x)) t) ∧
      (∀ t x, U t (H x) = H (U t x)) := by
  have hcont : Continuous U := continuous_of_strongly_continuous U hstrong
  obtain ⟨B, hB⟩ := exists_generator_of_continuous U hgroup hone hcont
  have hcomm : ∀ t, U t * B = B * U t := generator_comm U B hgroup hone hB
  -- pointwise derivatives
  have hBx : ∀ t x, HasDerivAt (fun r => U r x) ((U t * B) x) t := by
    intro t x
    have hl := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ) (x := U t)
    simpa [Function.comp] using hl.comp_hasDerivAt t (hB t)
  have hskew : star B = -B := by
    refine star_eq_neg_of_unitary U B hone hunitary ?_
    intro x
    have := hBx 0 x
    simpa [hone] using this
  refine ⟨Complex.I • B, ?_, ?_, ?_⟩
  · show star (Complex.I • B) = Complex.I • B
    rw [star_smul, hskew]
    simp
  · intro t x
    have h := hBx t x
    have hval : -Complex.I • (Complex.I • B) (U t x) = (U t * B) x := by
      have : (U t * B) x = (B * U t) x := by rw [hcomm t]
      rw [this]
      simp [smul_smul, Complex.I_mul_I]
    rw [hval]
    exact h
  · intro t x
    have : (U t * B) x = (B * U t) x := by rw [hcomm t]
    simpa using this

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

