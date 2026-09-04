/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-! ## Minkowski spacetime -/

/-- Minkowski spacetime `ℝ⁴`, with coordinates indexed by `Fin 4`
(coordinate `0` is time, coordinates `1,2,3` are space). -/
abbrev Spacetime : Type := Fin 4 → ℝ

/-- The Minkowski quadratic form with signature `(+,-,-,-)`. -/
def minkowskiSq (v : Spacetime) : ℝ :=
  (v 0) ^ 2 - ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2)

/-- Two spacetime points are *spacelike separated* when their difference has
negative Minkowski square. -/
def Spacelike (x y : Spacetime) : Prop := minkowskiSq (x - y) < 0

/-- The unit vector in the first spatial direction. -/
def spatialUnit : Spacetime := fun i => if i = 1 then 1 else 0

/-- Points displaced from `x` by a nonzero purely spatial vector are spacelike
separated from `x`. -/
lemma spacelike_spatial_shift (x : Spacetime) {c : ℝ} (hc : c ≠ 0) :
    Spacelike x (x + c • spatialUnit) := by
  have h : x - (x + c • spatialUnit) = (-c) • spatialUnit := by
    funext i; simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]; ring
  simp only [Spacelike, h, minkowskiSq, Pi.smul_apply, spatialUnit]
  norm_num
  positivity

/-- The spatially displaced points converge to `x`. -/
lemma tendsto_spatial_shift (x : Spacetime) :
    Filter.Tendsto (fun k : ℕ => x + (1 / (k + 1 : ℝ)) • spatialUnit)
      Filter.atTop (nhds x) := by
  have h0 : Filter.Tendsto (fun k : ℕ => (1 / (k + 1 : ℝ))) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Filter.Tendsto (fun k : ℕ => (1 / (k + 1 : ℝ)) • spatialUnit)
      Filter.atTop (nhds ((0 : ℝ) • spatialUnit)) := h0.smul_const spatialUnit
  have h2 := Filter.Tendsto.const_add x h1
  simpa using h2

/-! ## The spin–statistics connection

We work with a quantum field `φ` on a complex inner product space `H` with a
distinguished vacuum vector `Ω`.  The hypotheses below are the standard
Wightman inputs used in the proof of the spin–statistics theorem:

* `hherm` : the smeared field operators are hermitian;
* `hloc`  : *locality with statistics sign* `σ`: at spacelike separation the
  field operators commute (`σ = 1`, Bose statistics) or anticommute
  (`σ = -1`, Fermi statistics);
* `hsym`  : the *two point Wightman function* `W x y = ⟪Ω, φ x (φ y Ω)⟫`
  satisfies `W x y = (-1)^n * W y x` at spacelike separation, where `n = 2s`
  is twice the spin.  This is the consequence of Lorentz covariance and the
  spectral condition (Bargmann–Hall–Wightman symmetry) that carries the spin
  dependence;
* `hcont` : the two point function is continuous;
* `hnontriv` : the field is not identically trivial on the vacuum.

The conclusion is the spin–statistics connection: the statistics sign is forced
to be `(-1)^(2s)`, i.e. integer spin fields are bosons and half-integer spin
fields are fermions. -/
theorem spin_statistics
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ω : H) (φ : Spacetime → H → H) (n : ℕ) (σ : ℂ)
    (hσ : σ = 1 ∨ σ = -1)
    (hherm : ∀ (x : Spacetime) (u v : H),
      (inner u (φ x v) : ℂ) = (inner (φ x u) v : ℂ))
    (hloc : ∀ x y : Spacetime, Spacelike x y → ∀ v : H, φ x (φ y v) = σ • φ y (φ x v))
    (hsym : ∀ x y : Spacetime, Spacelike x y →
      (inner Ω (φ x (φ y Ω)) : ℂ) = (-1 : ℂ) ^ n * (inner Ω (φ y (φ x Ω)) : ℂ))
    (hcont : ∀ x : Spacetime, Continuous fun y : Spacetime => (inner Ω (φ x (φ y Ω)) : ℂ))
    (hnontriv : ∃ x : Spacetime, φ x Ω ≠ 0) :
    σ = (-1 : ℂ) ^ n := by
  by_contra hne
  -- wrong statistics: `σ = -(-1)^n`
  have hsg : σ = -((-1 : ℂ) ^ n) := by
    rcases Nat.even_or_odd n with he | ho
    · have hp : (-1 : ℂ) ^ n = 1 := he.neg_one_pow
      rcases hσ with h | h
      · exact absurd (by rw [h, hp]) hne
      · rw [h, hp]
    · have hp : (-1 : ℂ) ^ n = -1 := ho.neg_one_pow
      rcases hσ with h | h
      · rw [h, hp]; ring
      · exact absurd (by rw [h, hp]) hne
  -- the two point function vanishes at spacelike separation
  have hvan : ∀ x y : Spacetime, Spacelike x y → (inner Ω (φ x (φ y Ω)) : ℂ) = 0 := by
    intro x y hxy
    have h1 : (inner Ω (φ x (φ y Ω)) : ℂ) = σ * (inner Ω (φ y (φ x Ω)) : ℂ) := by
      rw [hloc x y hxy Ω, inner_smul_right]
    have h2 := hsym x y hxy
    rw [hsg] at h1
    have : (2 : ℂ) * (inner Ω (φ x (φ y Ω)) : ℂ) = 0 := by
      rw [h2] at h1 ⊢; ring_nf; ring_nf at h1; linear_combination h1
    simpa using this
  -- hence, by continuity, it vanishes on the diagonal
  obtain ⟨x, hx⟩ := hnontriv
  have hdiag : (inner Ω (φ x (φ x Ω)) : ℂ) = 0 := by
    have hlim := (hcont x).continuousAt.tendsto.comp (tendsto_spatial_shift x)
    have hzero : (fun k : ℕ =>
        (inner Ω (φ x (φ (x + (1 / (k + 1 : ℝ)) • spatialUnit) Ω)) : ℂ)) = fun _ => 0 := by
      funext k
      refine hvan _ _ (spacelike_spatial_shift x ?_)
      positivity
    rw [Function.comp_def] at hlim
    rw [hzero] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  -- but the diagonal value is the squared norm of `φ x Ω`
  have hnorm : (inner Ω (φ x (φ x Ω)) : ℂ) = ((‖φ x Ω‖ : ℂ)) ^ 2 := by
    rw [hherm x Ω (φ x Ω)]
    exact inner_self_eq_norm_sq_to_K
  rw [hnorm] at hdiag
  have : ‖φ x Ω‖ = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hdiag
    exact_mod_cast this
  exact hx (norm_eq_zero.1 this)

/-- Sanity check: the hypotheses of `Frontier.spin_statistics` are consistent.
The one dimensional space `H = ℂ` with vacuum `1`, field `φ x v = v`, spin `0`
and Bose statistics `σ = 1` satisfies all of them. -/
theorem spin_statistics_consistent :
    ∃ (Ω : ℂ) (φ : Spacetime → ℂ → ℂ) (n : ℕ) (σ : ℂ),
      (σ = 1 ∨ σ = -1) ∧
      (∀ (x : Spacetime) (u v : ℂ), (inner u (φ x v) : ℂ) = (inner (φ x u) v : ℂ)) ∧
      (∀ x y : Spacetime, Spacelike x y → ∀ v : ℂ, φ x (φ y v) = σ • φ y (φ x v)) ∧
      (∀ x y : Spacetime, Spacelike x y →
        (inner Ω (φ x (φ y Ω)) : ℂ) = (-1 : ℂ) ^ n * (inner Ω (φ y (φ x Ω)) : ℂ)) ∧
      (∀ x : Spacetime, Continuous fun y : Spacetime => (inner Ω (φ x (φ y Ω)) : ℂ)) ∧
      (∃ x : Spacetime, φ x Ω ≠ 0) ∧ σ = (-1 : ℂ) ^ n := by
  refine ⟨1, fun _ v => v, 0, 1, Or.inl rfl, ?_, ?_, ?_, ?_, ⟨0, one_ne_zero⟩, by norm_num⟩
  · intro x u v; simp [RCLike.inner_apply, mul_comm]
  · intro x y _ v; simp
  · intro x y _; simp
  · intro x; simpa using continuous_const

end Frontier

