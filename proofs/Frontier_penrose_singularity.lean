/-
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
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

/-!
## Formalization notes

Mathlib currently has no Lorentzian causal theory (no trapped surfaces, no null
geodesic congruences, no global hyperbolicity), so the full Penrose singularity
theorem cannot be stated verbatim.  What is formalized here is its analytic
heart, the *focusing theorem*, which is the step at which the geometry actually
produces incompleteness:

* a null geodesic congruence orthogonal to a two-surface has an *expansion*
  `θ` as a function of the affine parameter;
* the **trapped surface** hypothesis says the initial expansion is negative,
  `θ 0 < 0`;
* the **null energy condition**, fed into the Raychaudhuri equation
  `θ' = -θ²/2 - σ² - Ric(k,k)` (with the shear term `σ² ≥ 0`), gives the
  differential inequality `θ' ≤ -θ²/2`;
* the conclusion is that the congruence cannot be smoothly extended past affine
  parameter `2/|θ 0|`: a focal point (caustic) must occur first.  Equivalently,
  no *complete* congruence with these properties exists, which is the sense in
  which the spacetime is null geodesically incomplete.

`Frontier.penrose_singularity` is the quantitative focusing statement; the
corollary `Frontier.penrose_singularity_incomplete` states the resulting
incompleteness: the hypotheses cannot hold for all affine parameters `t ≥ 0`.
-/

/-- **Penrose focusing / singularity theorem (analytic core).**

If the expansion `θ` of a null geodesic congruence is defined and differentiable
on the affine interval `[0, L]`, satisfies the Raychaudhuri inequality
`θ' t ≤ -(θ t)^2 / 2` there (this is where the null energy condition enters),
and starts out negative, `θ 0 < 0` (the trapped surface condition), then
`L < 2 / (-θ 0)`: the congruence must develop a focal point within affine
parameter `2 / |θ 0|`, so it cannot be extended indefinitely. -/
theorem penrose_singularity {θ θ' : ℝ → ℝ} {L : ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) L, HasDerivAt θ (θ' t) t)
    (hRay : ∀ t ∈ Set.Icc (0 : ℝ) L, θ' t ≤ -(θ t) ^ 2 / 2)
    (htrap : θ 0 < 0) :
    L < 2 / (-θ 0) := by
  by_contra hcon
  push_neg at hcon
  set a : ℝ := θ 0 with ha_def
  have ha : a < 0 := htrap
  set T : ℝ := 2 / (-a) with hT_def
  have hT : 0 < T := div_pos (by norm_num) (by linarith)
  have hsub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) L := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 hcon⟩
  -- continuity of `θ` on `[0, T]`
  have hcont : ContinuousOn θ (Set.Icc (0 : ℝ) T) := fun x hx =>
    ((hderiv x (hsub hx)).continuousAt).continuousWithinAt
  have hint : interior (Set.Icc (0 : ℝ) T) = Set.Ioo 0 T := interior_Icc
  -- Step 1: `θ` is nonincreasing on `[0, T]`, hence stays `≤ a < 0`.
  have hanti : AntitoneOn θ (Set.Icc (0 : ℝ) T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcont
      (f' := θ') (fun x hx => ?_) (fun x hx => ?_)
    · rw [hint] at hx
      exact (hderiv x (hsub (Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩))).hasDerivWithinAt
    · rw [hint] at hx
      have := hRay x (hsub (Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩))
      nlinarith [sq_nonneg (θ x)]
  have hneg : ∀ t ∈ Set.Icc (0 : ℝ) T, θ t ≤ a := by
    intro t ht
    exact hanti (Set.mem_Icc.mpr ⟨le_refl 0, hT.le⟩) ht ht.1
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) T, θ t < 0 := fun t ht =>
    lt_of_le_of_lt (hneg t ht) ha
  -- Step 2: `w t = (θ t)⁻¹ - t/2` is nondecreasing on `[0, T]`.
  set w : ℝ → ℝ := fun t => (θ t)⁻¹ - t / 2 with hw_def
  set w' : ℝ → ℝ := fun t => -θ' t / (θ t) ^ 2 - 1 / 2 with hw'_def
  have hwderiv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt w (w' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => (θ s)⁻¹) (-θ' t / (θ t) ^ 2) t :=
      (hderiv t (hsub ht)).inv (ne_of_lt (hne t ht))
    have h2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).div_const 2)
    simpa [hw_def, hw'_def] using h1.sub h2
  have hwcont : ContinuousOn w (Set.Icc (0 : ℝ) T) := fun x hx =>
    ((hwderiv x hx).continuousAt).continuousWithinAt
  have hmono : MonotoneOn w (Set.Icc (0 : ℝ) T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hwcont
      (f' := w') (fun x hx => ?_) (fun x hx => ?_)
    · rw [hint] at hx
      exact (hwderiv x (Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩)).hasDerivWithinAt
    · rw [hint] at hx
      have hx' : x ∈ Set.Icc (0 : ℝ) T := Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩
      have hray := hRay x (hsub hx')
      have hθ : θ x < 0 := hne x hx'
      have hsq : 0 < (θ x) ^ 2 := by nlinarith
      have hhalf : (1 : ℝ) / 2 ≤ -θ' x / (θ x) ^ 2 := by
        rw [le_div_iff₀ hsq]
        nlinarith
      rw [hw'_def]
      simp only [sub_nonneg]
      linarith
  -- Step 3: contradiction at `t = T`.
  have hkey : w 0 ≤ w T :=
    hmono (Set.mem_Icc.mpr ⟨le_refl 0, hT.le⟩) (Set.mem_Icc.mpr ⟨hT.le, le_refl T⟩) hT.le
  have hT2 : T / 2 = -a⁻¹ := by
    rw [hT_def]
    field_simp
  have hw0 : w 0 = a⁻¹ := by simp [hw_def, ha_def]
  have hwT : w T = (θ T)⁻¹ + a⁻¹ := by rw [hw_def]; simp [hT2]
  have hTneg : (θ T)⁻¹ < 0 := inv_lt_zero.mpr (hne T (Set.mem_Icc.mpr ⟨hT.le, le_refl T⟩))
  rw [hw0, hwT] at hkey
  linarith

/-- **Null geodesic incompleteness.**  There is no expansion function for a null
geodesic congruence that is defined for *all* affine parameters `t ≥ 0`, obeys
the Raychaudhuri inequality coming from the null energy condition, and starts
from a trapped surface (`θ 0 < 0`).  Thus such a congruence must terminate at a
finite affine parameter: the spacetime is null geodesically incomplete. -/
theorem penrose_singularity_incomplete {θ θ' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt θ (θ' t) t)
    (hRay : ∀ t ∈ Set.Ici (0 : ℝ), θ' t ≤ -(θ t) ^ 2 / 2)
    (htrap : θ 0 < 0) : False := by
  set L : ℝ := 2 / (-θ 0) with hL_def
  have hpos : 0 < L := div_pos (by norm_num) (by linarith)
  have := penrose_singularity (θ := θ) (θ' := θ') (L := L)
    (fun t ht => hderiv t (Set.mem_Ici.mpr ht.1))
    (fun t ht => hRay t (Set.mem_Ici.mpr ht.1)) htrap
  exact absurd this (lt_irrefl L)

end Frontier

