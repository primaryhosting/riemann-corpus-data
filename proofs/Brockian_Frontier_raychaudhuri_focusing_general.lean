import Mathlib

/-!
# Brockian packaging of the Hawking focusing / singularity argument

This file contains

* `Brockian.Frontier.raychaudhuri_focusing_general`: the analytic core.  If a real function
  `theta` ("expansion") satisfies a Raychaudhuri-type differential inequality
  `theta' ≤ -theta ^ 2 / n` on `[0, L)` and starts negative, then `L ≤ -n / theta 0`.
  The constant `n` is the number of transverse dimensions: `n = 3` for a timelike
  congruence in `3 + 1` dimensions (Hawking), `n = 2` for a null congruence (Penrose).

* `Brockian.Frontier.TimelikeCongruence` and `Brockian.Frontier.hawking_focusing`: the
  timelike (`n = 3`) packaging requested, and its proof.

* `Brockian.Frontier.NullCongruence` and `Brockian.Frontier.penrose_focusing`: the null
  (`n = 2`) specialisation, for comparison.

* `Brockian.Frontier.ExpandingCauchy`, `Brockian.Frontier.TimelikeGeodesicallyComplete`
  and `Brockian.Frontier.hawking_singularity`: a geometric packaging of the cosmological
  setting.  Since Mathlib has no Lorentzian geometry, the packaging is *abstract*: the
  data of a Cauchy surface with a uniformly expanding orthogonal geodesic congruence is
  recorded as the family of expansion scalars along the generators together with the
  Raychaudhuri inequality (which encodes the strong energy condition and vanishing
  vorticity) and the uniform expansion bound `theta i 0 ≤ -c < 0`.  Timelike geodesic
  completeness is taken in the form it is actually used in Hawking's argument: every
  generator can be continued, with a smooth expansion scalar, to arbitrarily large proper
  time.  The theorem says this is impossible.
-/

namespace Brockian.Frontier

open Set

/-! ### The analytic focusing lemma -/

/-- **Raychaudhuri focusing, general transverse dimension.**

If `theta : ℝ → ℝ` has derivative `dtheta` on `[0, L)`, satisfies the Raychaudhuri
inequality `dtheta τ ≤ -(theta τ) ^ 2 / n` there (`n > 0`), and is negative at `τ = 0`,
then the interval on which this is possible has length at most `-n / theta 0`.

Proof: `theta` is antitone, hence stays `≤ theta 0 < 0`; therefore `1 / theta` is
differentiable with derivative `-dtheta / theta ^ 2 ≥ 1 / n`, so
`1 / theta τ ≥ 1 / theta 0 + τ / n`, while `1 / theta τ < 0`. -/
theorem raychaudhuri_focusing_general {L n : ℝ} {theta dtheta : ℝ → ℝ} (hn : 0 < n)
    (hderiv : ∀ τ ∈ Ico (0 : ℝ) L, HasDerivAt theta (dtheta τ) τ)
    (hRay : ∀ τ ∈ Ico (0 : ℝ) L, dtheta τ ≤ -(theta τ) ^ 2 / n)
    (h0 : theta 0 < 0) :
    L ≤ -n / theta 0 := by
  have hbound : 0 < -n / theta 0 := div_pos_of_neg_of_neg (by linarith) h0
  -- `theta` is antitone on `[0, L)`
  have hcont : ContinuousOn theta (Ico 0 L) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hsub : Ioo (0 : ℝ) L ⊆ Ico (0 : ℝ) L := Ioo_subset_Ico_self
  have hanti : AntitoneOn theta (Ico 0 L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico 0 L) hcont ?_ ?_
    · intro x hx
      rw [interior_Ico] at hx
      exact (hderiv x (hsub hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hderiv x (hsub hx)).deriv]
      have hR := hRay x (hsub hx)
      have h2 : 0 ≤ (theta x) ^ 2 / n := div_nonneg (sq_nonneg _) hn.le
      rw [neg_div] at hR
      linarith
  have hmem0 : ∀ τ ∈ Ico (0 : ℝ) L, (0 : ℝ) ∈ Ico (0 : ℝ) L := fun τ hτ =>
    ⟨le_refl 0, lt_of_le_of_lt hτ.1 hτ.2⟩
  have hneg : ∀ τ ∈ Ico (0 : ℝ) L, theta τ ≤ theta 0 := fun τ hτ =>
    hanti (hmem0 τ hτ) hτ hτ.1
  -- the reciprocal, corrected by `τ / n`, is monotone
  set w : ℝ → ℝ := fun τ => (theta τ)⁻¹ - τ / n with hw
  have hwderiv : ∀ x ∈ Ioo (0 : ℝ) L,
      HasDerivAt w (-dtheta x / (theta x) ^ 2 - 1 / n) x := by
    intro x hx
    have hx' := hsub hx
    have hne : theta x ≠ 0 := ne_of_lt (lt_of_le_of_lt (hneg x hx') h0)
    exact ((hderiv x hx').inv hne).sub ((hasDerivAt_id x).div_const n)
  have hwcont : ContinuousOn w (Ico 0 L) := by
    intro x hx
    have hne : theta x ≠ 0 := ne_of_lt (lt_of_le_of_lt (hneg x hx) h0)
    exact HasDerivAt.continuousAt
      (((hderiv x hx).inv hne).sub ((hasDerivAt_id x).div_const n)) |>.continuousWithinAt
  have hwmono : MonotoneOn w (Ico 0 L) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 L) hwcont ?_ ?_
    · intro x hx
      rw [interior_Ico] at hx
      exact (hwderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hwderiv x hx).deriv]
      have hx' := hsub hx
      have hlt : theta x < 0 := lt_of_le_of_lt (hneg x hx') h0
      have hsq : 0 < (theta x) ^ 2 := by nlinarith
      have hR := hRay x hx'
      rw [neg_div] at hR
      rw [sub_nonneg, le_div_iff₀ hsq]
      have hmul : (1 : ℝ) / n * (theta x) ^ 2 = (theta x) ^ 2 / n := by ring
      rw [hmul]
      linarith
  -- conclude
  have key : ∀ τ ∈ Ico (0 : ℝ) L, τ < -n / theta 0 := by
    intro τ hτ
    have hmono := hwmono (hmem0 τ hτ) hτ hτ.1
    have hlt : theta τ < 0 := lt_of_le_of_lt (hneg τ hτ) h0
    have hinvneg : (theta τ)⁻¹ < 0 := inv_lt_zero'.2 hlt
    have hinv0 : (theta 0)⁻¹ < 0 := inv_lt_zero'.2 h0
    simp only [hw, zero_div, sub_zero] at hmono
    have hτn : τ / n < -(theta 0)⁻¹ := by linarith
    have : τ < -(theta 0)⁻¹ * n := by
      rw [div_lt_iff₀ hn] at hτn; linarith
    calc τ < -(theta 0)⁻¹ * n := this
      _ = -n / theta 0 := by field_simp
  by_contra hcon
  push_neg at hcon
  exact absurd (key (-n / theta 0) ⟨le_of_lt hbound, hcon⟩) (lt_irrefl _)

/-- Shifted form of the focusing lemma, the step needed for the Hawking–Penrose
unification: a congruence obeying the Raychaudhuri inequality on all of `[0, ∞)` cannot
have negative expansion at *any* time.  (In Hawking–Penrose the genericity condition is
what forces the expansion to become negative somewhere along each complete causal
geodesic; this lemma turns that into a contradiction.) -/
theorem no_complete_congruence_of_negative_expansion {n τ₀ : ℝ} {theta dtheta : ℝ → ℝ}
    (hn : 0 < n) (hderiv : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt theta (dtheta τ) τ)
    (hRay : ∀ τ : ℝ, 0 ≤ τ → dtheta τ ≤ -(theta τ) ^ 2 / n)
    (hτ₀ : 0 ≤ τ₀) (hneg : theta τ₀ < 0) : False := by
  set g : ℝ → ℝ := fun s => theta (τ₀ + s) with hg
  set dg : ℝ → ℝ := fun s => dtheta (τ₀ + s) with hdg
  set L : ℝ := -n / theta τ₀ + 1 with hL
  have hgderiv : ∀ s ∈ Ico (0 : ℝ) L, HasDerivAt g (dg s) s := by
    intro s hs
    have hs0 : 0 ≤ τ₀ + s := by linarith [hs.1]
    have h := (hderiv (τ₀ + s) hs0).comp s ((hasDerivAt_id s).const_add τ₀)
    simpa [hg, hdg, Function.comp] using h
  have hgRay : ∀ s ∈ Ico (0 : ℝ) L, dg s ≤ -(g s) ^ 2 / n := by
    intro s hs
    exact hRay (τ₀ + s) (by linarith [hs.1])
  have hg0 : g 0 < 0 := by simpa [hg] using hneg
  have hbound := raychaudhuri_focusing_general hn hgderiv hgRay hg0
  simp only [hg, add_zero] at hbound
  rw [hL] at hbound
  linarith

/-! ### The timelike (Hawking) packaging -/

/-- Timelike expansion of a vorticity-free congruence on a proper-time interval `[0, L)`
in `3 + 1` dimensions.  `hRay` is the Raychaudhuri inequality: it encodes the strong
energy condition (`Ric(u,u) ≥ 0`), vanishing vorticity and the trace inequality
`σ_{ab}σ^{ab} ≥ 0`.  `htrapped` says the congruence is initially converging. -/
structure TimelikeCongruence (L : ℝ) where
  theta : ℝ → ℝ
  dtheta : ℝ → ℝ
  hderiv : ∀ τ ∈ Set.Ico (0 : ℝ) L, HasDerivAt theta (dtheta τ) τ
  hRay : ∀ τ ∈ Set.Ico (0 : ℝ) L, dtheta τ ≤ -(theta τ) ^ 2 / 3
  htrapped : theta 0 < 0

/-- **Hawking focusing lemma.**  A vorticity-free timelike congruence in `3 + 1`
dimensions with initial expansion `theta 0 < 0` develops a conjugate point within proper
time `-3 / theta 0`; equivalently, the length of an interval carrying such a congruence
is at most `-3 / theta 0`.

(The hypothesis `0 < L` of the original sketch is not needed: for `L ≤ 0` the bound holds
trivially since `-3 / theta 0 > 0`.) -/
theorem hawking_focusing {L : ℝ} (C : TimelikeCongruence L) :
    L ≤ -3 / C.theta 0 :=
  raychaudhuri_focusing_general (by norm_num) C.hderiv C.hRay C.htrapped

/-- The focusing bound of `hawking_focusing` is sharp: the exact solution
`theta τ = 3 / (τ - 1)` of `theta' = -theta ^ 2 / 3` is a timelike congruence on `[0, 1)`
with `theta 0 = -3`, and there `L = 1 = -3 / theta 0`. -/
theorem hawking_focusing_sharp :
    ∃ C : TimelikeCongruence 1, (1 : ℝ) = -3 / C.theta 0 := by
  refine ⟨{ theta := fun τ => 3 / (τ - 1)
            dtheta := fun τ => -3 / (τ - 1) ^ 2
            hderiv := ?_
            hRay := ?_
            htrapped := by norm_num }, by norm_num⟩
  · intro x hx
    have hne : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx.2)
    have h := (hasDerivAt_id x).sub_const 1
    have h2 := (hasDerivAt_const x (3 : ℝ)).div h hne
    simp only [id] at h2
    convert h2 using 1
    ring
  · intro x hx
    have hne : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx.2)
    have heq : -(3 / (x - 1)) ^ 2 / 3 = -3 / (x - 1) ^ 2 := by field_simp
    rw [heq]

/-! ### The null (Penrose) specialisation, for comparison -/

/-- Null expansion of a vorticity-free congruence on an affine interval `[0, L)`:
the same data with the transverse dimension `2` instead of `3`. -/
structure NullCongruence (L : ℝ) where
  theta : ℝ → ℝ
  dtheta : ℝ → ℝ
  hderiv : ∀ τ ∈ Set.Ico (0 : ℝ) L, HasDerivAt theta (dtheta τ) τ
  hRay : ∀ τ ∈ Set.Ico (0 : ℝ) L, dtheta τ ≤ -(theta τ) ^ 2 / 2
  htrapped : theta 0 < 0

/-- **Penrose (null) focusing lemma**: only the numerical constant differs. -/
theorem penrose_focusing {L : ℝ} (C : NullCongruence L) :
    L ≤ -2 / C.theta 0 :=
  raychaudhuri_focusing_general (by norm_num) C.hderiv C.hRay C.htrapped

/-! ### Geometric packaging: the cosmological setting -/

/-- Abstract data of a Cauchy surface `Σ` whose orthogonal (hence vorticity-free) future
timelike geodesic congruence is everywhere contracting at a uniform rate.

* `ι` indexes the generators, i.e. the points of `Σ`; `Nonempty ι` says `Σ ≠ ∅`.
* `theta i τ` is the expansion of the congruence at proper time `τ` along the generator
  through `i`, `dtheta i` its derivative.
* `hRay` is the Raychaudhuri inequality along each generator, valid wherever the
  expansion is defined and differentiable; it encodes the strong energy condition,
  vanishing vorticity and `σ_{ab}σ^{ab} ≥ 0`.
* `hexpand` is the uniform expansion bound `theta i 0 ≤ -c < 0` on `Σ`
  (in the time-reversed, cosmological reading: `Σ` expands everywhere at rate `≥ c`).

No Lorentzian geometry is available in Mathlib, so the differential-geometric content is
represented by exactly the data the focusing argument consumes. -/
structure ExpandingCauchy (ι : Type*) where
  /-- the surface is nonempty -/
  hne : Nonempty ι
  /-- expansion scalar along each generator -/
  theta : ι → ℝ → ℝ
  /-- its proper-time derivative -/
  dtheta : ι → ℝ → ℝ
  /-- uniform bound on the initial expansion -/
  c : ℝ
  hc : 0 < c
  /-- Raychaudhuri inequality (strong energy condition, zero vorticity) -/
  hRay : ∀ (i : ι), ∀ τ : ℝ, 0 ≤ τ → dtheta i τ ≤ -(theta i τ) ^ 2 / 3
  /-- uniform initial contraction (expansion of `Σ` in the time-reversed reading) -/
  hexpand : ∀ i : ι, theta i 0 ≤ -c

/-- Timelike geodesic completeness, in the form used by the focusing argument: every
generator of the congruence extends to all future proper times with a differentiable
expansion scalar. -/
def TimelikeGeodesicallyComplete {ι : Type*} (C : ExpandingCauchy ι) : Prop :=
  ∀ (i : ι), ∀ τ : ℝ, 0 ≤ τ → HasDerivAt (C.theta i) (C.dtheta i τ) τ

/-- **Hawking singularity theorem (quantitative reduction).**  A spacetime containing a
Cauchy surface whose orthogonal geodesic congruence is uniformly contracting, and which
satisfies the strong energy condition, is not timelike geodesically complete: every
generator terminates (in a conjugate point / focal singularity) within proper time
`3 / c`. -/
theorem hawking_singularity {ι : Type*} (C : ExpandingCauchy ι) :
    ¬ TimelikeGeodesicallyComplete C := by
  intro hcomplete
  obtain ⟨i⟩ := C.hne
  set L : ℝ := 3 / C.c + 1 with hL
  have h0 : C.theta i 0 < 0 := lt_of_le_of_lt (C.hexpand i) (by linarith [C.hc])
  have hbound : L ≤ -3 / C.theta i 0 :=
    raychaudhuri_focusing_general (n := 3) (by norm_num)
      (fun τ hτ => hcomplete i τ hτ.1) (fun τ hτ => C.hRay i τ hτ.1) h0
  -- but `-3 / theta i 0 ≤ 3 / c < L`
  have hθ : C.c ≤ -C.theta i 0 := by linarith [C.hexpand i]
  have heq : -3 / C.theta i 0 = 3 / (-C.theta i 0) := by rw [div_neg, ← neg_div]
  have hle : -3 / C.theta i 0 ≤ 3 / C.c := by
    rw [heq]
    exact div_le_div_of_nonneg_left (by norm_num) C.hc hθ
  rw [hL] at hbound
  linarith

/-- Sanity check: the hypotheses of `ExpandingCauchy` are satisfiable, so
`hawking_singularity` is not vacuous.  (In this toy datum the expansion is the constant
`-1`; it is completeness, i.e. the requirement that `dtheta` really is the derivative of
`theta` for all future proper times, that fails.) -/
example : ExpandingCauchy Unit :=
  { hne := ⟨()⟩
    theta := fun _ _ => -1
    dtheta := fun _ _ => -1
    c := 1
    hc := one_pos
    hRay := by intro i τ _; norm_num
    hexpand := by intro i; norm_num }

end Brockian.Frontier

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

