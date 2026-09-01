import Mathlib
/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Stone's theorem: the generator of a one-parameter unitary group is self-adjoint

Let `H` be a complex Hilbert space and let `U : ℝ → H →L[ℂ] H` be a one-parameter group of
unitary operators (`U (s + t) = U s ∘L U t`, each `U t` unitary) which is differentiable at
`t = 0` in the strong sense, with (bounded) generator `A`, i.e.
`HasDerivAt (fun t => U t x) (A x) 0` for every `x`.

Then `A` is skew-adjoint and consequently the physical generator `i • A` (equivalently, the
Hamiltonian, up to sign conventions) is self-adjoint:  `IsSelfAdjoint (Complex.I • A)`.

Strong continuity of `t ↦ U t x` is *not* assumed: it is derived below
(`QPhys.stone_stronglyContinuous`) from the group law together with differentiability at `0`.
-/

namespace QPhys

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A one-parameter group of unitaries is the identity at `t = 0`. -/
theorem unitary_group_apply_zero {U : ℝ → H →L[ℂ] H}
    (hgroup : ∀ s t, U (s + t) = U s ∘L U t)
    (hunitary : ∀ t, U t ∈ unitary (H →L[ℂ] H)) :
    U 0 = 1 := by
  have h1 : U 0 * U 0 = U 0 := by
    have := hgroup 0 0
    simp only [add_zero] at this
    exact this.symm
  have h2 : star (U 0) * U 0 = 1 := (Unitary.mem_iff.mp (hunitary 0)).1
  calc U 0 = (star (U 0) * U 0) * U 0 := by rw [h2, one_mul]
    _ = star (U 0) * (U 0 * U 0) := by rw [mul_assoc]
    _ = star (U 0) * U 0 := by rw [h1]
    _ = 1 := h2

/-- Unitaries preserve the inner product. -/
theorem unitary_inner_map {V : H →L[ℂ] H} (hV : V ∈ unitary (H →L[ℂ] H)) (x y : H) :
    ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ := by
  have h2 : star V * V = 1 := (Unitary.mem_iff.mp hV).1
  have : ⟪x, (ContinuousLinearMap.adjoint V) (V y)⟫_ℂ = ⟪V x, V y⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_right V x (V y)
  rw [← this]
  have : (ContinuousLinearMap.adjoint V) (V y) = (star V * V) y := by
    rw [ContinuousLinearMap.star_eq_adjoint]; rfl
  rw [this, h2]
  rfl

/-- **Stone's theorem** (bounded-generator form).  The generator `A` of a one-parameter unitary
group is skew-adjoint: `⟪A x, y⟫ + ⟪x, A y⟫ = 0`. -/
theorem stone_skew_adjoint {U : ℝ → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hgroup : ∀ s t, U (s + t) = U s ∘L U t)
    (hunitary : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hderiv : ∀ x : H, HasDerivAt (fun t => U t x) (A x) 0) (x y : H) :
    ⟪A x, y⟫_ℂ + ⟪x, A y⟫_ℂ = 0 := by
  have h0 : U 0 = 1 := unitary_group_apply_zero hgroup hunitary
  have hconst : (fun t : ℝ => ⟪U t x, U t y⟫_ℂ) = fun _ : ℝ => ⟪x, y⟫_ℂ := by
    funext t
    exact unitary_inner_map (hunitary t) x y
  have hd : HasDerivAt (fun t : ℝ => ⟪U t x, U t y⟫_ℂ)
      (⟪U 0 x, A y⟫_ℂ + ⟪A x, U 0 y⟫_ℂ) 0 := (hderiv x).inner ℂ (hderiv y)
  rw [hconst] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (⟪x, y⟫_ℂ))
  rw [h0] at this
  simp only [ContinuousLinearMap.one_apply] at this
  rw [← this]
  ring

/-- **Stone's theorem**: a strongly differentiable one-parameter unitary group has a
self-adjoint generator.  Concretely, if `U` is a one-parameter group of unitaries on a complex
Hilbert space with (bounded) generator `A`, then `Complex.I • A` is self-adjoint. -/
theorem stone_generator {U : ℝ → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hgroup : ∀ s t, U (s + t) = U s ∘L U t)
    (hunitary : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hderiv : ∀ x : H, HasDerivAt (fun t => U t x) (A x) 0) :
    IsSelfAdjoint (Complex.I • A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have h := stone_skew_adjoint hgroup hunitary hderiv x y
  have hxy : ⟪A x, y⟫_ℂ = -⟪x, A y⟫_ℂ := by linear_combination h
  show ⟪(Complex.I • A) x, y⟫_ℂ = ⟪x, (Complex.I • A) y⟫_ℂ
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_I, hxy]
  ring

omit [CompleteSpace H] in
/-- Strong continuity is automatic in the above setting: differentiability at `0` together with
the group law forces `t ↦ U t x` to be continuous everywhere. -/
theorem stone_stronglyContinuous {U : ℝ → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hgroup : ∀ s t, U (s + t) = U s ∘L U t)
    (hderiv : ∀ x : H, HasDerivAt (fun t => U t x) (A x) 0) (x : H) :
    Continuous fun t : ℝ => U t x := by
  have hcont0 : ContinuousAt (fun t : ℝ => U t x) 0 := (hderiv x).continuousAt
  rw [continuous_iff_continuousAt]
  intro t
  have hrepr : (fun s : ℝ => U s x) = fun s : ℝ => U t (U (s - t) x) := by
    funext s
    have h := hgroup t (s - t)
    rw [add_sub_cancel] at h
    rw [h]
    rfl
  rw [hrepr]
  have hsub : ContinuousAt (fun s : ℝ => s - t) t :=
    (continuous_id.sub continuous_const).continuousAt
  have h1 : ContinuousAt (fun s : ℝ => U (s - t) x) t := by
    have h2 : ContinuousAt (fun r : ℝ => U r x) (t - t) := by simpa using hcont0
    have h3 := ContinuousAt.comp (g := fun r : ℝ => U r x) (f := fun s : ℝ => s - t) h2 hsub
    simpa [Function.comp] using h3
  exact (U t).continuous.continuousAt.comp h1

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

