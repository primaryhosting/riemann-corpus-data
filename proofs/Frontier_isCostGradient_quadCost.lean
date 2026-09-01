import Mathlib
/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-! ### The Ma–Trudinger–Wang condition (Loeper's form) -/

section MTW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic transport cost `c(x,y) = ‖x - y‖²/2`. -/
noncomputable def quadCost (x y : E) : ℝ := ‖x - y‖ ^ 2 / 2

/-- `G` is the field of `x`-gradients of the cost `c`, i.e. `G x y = ∇ₓ c(x,y)`. -/
def IsCostGradient (c : E → E → ℝ) (G : E → E → E) : Prop :=
  ∀ x y, HasGradientAt (fun x' => c x' y) (G x y) x

/-- A curve `y : ℝ → E` is a `c`-segment with base point `x₀` when the associated
momenta `∇ₓ c (x₀, y t)` depend affinely on `t`. -/
def IsCSegment (G : E → E → E) (x₀ : E) (y : ℝ → E) : Prop :=
  ∀ t : ℝ, G x₀ (y t) = (1 - t) • G x₀ (y 0) + t • G x₀ (y 1)

/-- **Loeper's maximum principle** for a cost `c` with `x`-gradient field `G`: along any
`c`-segment based at `x₀`, the function `t ↦ c(x₀, y t) - c(x, y t)` attains its maximum
at the endpoints.  For smooth non-degenerate costs this is equivalent to the
Ma–Trudinger–Wang condition `MTW(0)` (non-negative cross-curvature in the weak sense),
which is the structural hypothesis under which optimal maps are regular. -/
def LoeperMaxPrinciple (c : E → E → ℝ) (G : E → E → E) : Prop :=
  ∀ (x x₀ : E) (y : ℝ → E), IsCSegment G x₀ y → ∀ t ∈ Icc (0 : ℝ) 1,
    c x₀ (y t) - c x (y t) ≤
      max (c x₀ (y 0) - c x (y 0)) (c x₀ (y 1) - c x (y 1))

/-- The `x`-gradient of the quadratic cost is `x - y`. -/
theorem isCostGradient_quadCost :
    IsCostGradient (E := E) quadCost (fun x y => x - y) := by
  intro x y
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun x' : E => x' - y) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const y
  have h2 : HasFDerivAt (fun x' : E => ‖x' - y‖ ^ 2)
      (2 • ((innerSL ℝ (x - y)).comp (ContinuousLinearMap.id ℝ E))) x := h1.norm_sq
  have h3 : HasFDerivAt (fun x' : E => ‖x' - y‖ ^ 2 / 2)
      ((2 : ℝ)⁻¹ • (2 • ((innerSL ℝ (x - y)).comp (ContinuousLinearMap.id ℝ E)))) x := by
    simpa [div_eq_inv_mul] using h2.const_smul (2 : ℝ)⁻¹
  refine h3.congr_fderiv ?_
  ext z
  simp

/-- An affine function of `t` on `[0,1]` is bounded by the maximum of its endpoint values. -/
theorem affine_le_max {a b t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (1 - t) * a + t * b ≤ max a b := by
  nlinarith [le_max_left a b, le_max_right a b]

omit [CompleteSpace E] in
/-- The quadratic cost satisfies the Ma–Trudinger–Wang condition, in Loeper's form. -/
theorem quadCost_loeperMaxPrinciple :
    LoeperMaxPrinciple (E := E) quadCost (fun x y => x - y) := by
  intro x x₀ y hseg t ht
  have hy : y t = (1 - t) • y 0 + t • y 1 := by
    have h := hseg t
    simp only at h
    have h2 : (1 - t) • (x₀ - y 0) + t • (x₀ - y 1) = x₀ - ((1 - t) • y 0 + t • y 1) := by
      module
    rw [h2] at h
    exact sub_right_injective h
  -- the function `z ↦ c x₀ z - c x z` is affine in `z`
  have hval : ∀ z : E, quadCost x₀ z - quadCost x z
      = (‖x₀‖ ^ 2 - ‖x‖ ^ 2) / 2 - inner ℝ (x₀ - x) z := by
    intro z
    simp only [quadCost, norm_sub_sq_real, inner_sub_left]
    ring
  rw [hval (y t), hval (y 0), hval (y 1), hy]
  have hlin : inner ℝ (x₀ - x) ((1 - t) • y 0 + t • y 1)
      = (1 - t) * inner ℝ (x₀ - x) (y 0) + t * inner ℝ (x₀ - x) (y 1) := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hlin]
  have := affine_le_max (a := (‖x₀‖ ^ 2 - ‖x‖ ^ 2) / 2 - inner ℝ (x₀ - x) (y 0))
    (b := (‖x₀‖ ^ 2 - ‖x‖ ^ 2) / 2 - inner ℝ (x₀ - x) (y 1)) ht.1 ht.2
  linarith

end MTW

/-! ### One-dimensional regularity of optimal maps -/

/-- Two-point (`c`-cyclical) monotonicity for the quadratic cost forces monotonicity of the
transport map on the line. -/
theorem monotone_of_quadCost_cyclMonotone {T : ℝ → ℝ}
    (hopt : ∀ x y : ℝ,
      quadCost x (T x) + quadCost y (T y) ≤ quadCost x (T y) + quadCost y (T x)) :
    Monotone T := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  by_contra hcon
  push_neg at hcon
  have h := hopt x y
  simp only [quadCost, Real.norm_eq_abs, sq_abs] at h
  nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hcon)]

/-- An upper density bound gives an upper bound for the measure of an interval. -/
theorem withDensity_Icc_le {f : ℝ → ℝ≥0∞} {Lam : ℝ≥0} (hfub : ∀ x, f x ≤ Lam) (a b : ℝ) :
    (volume.withDensity f) (Icc a b) ≤ (Lam : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  rw [withDensity_apply _ measurableSet_Icc]
  calc ∫⁻ t in Icc a b, f t ≤ ∫⁻ _ in Icc a b, (Lam : ℝ≥0∞) :=
        lintegral_mono fun t => hfub t
    _ = (Lam : ℝ≥0∞) * volume (Icc a b) := setLIntegral_const _ _
    _ = (Lam : ℝ≥0∞) * ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]

/-- A lower density bound gives a lower bound for the measure of an interval. -/
theorem le_withDensity_Icc {g : ℝ → ℝ≥0∞} {lam : ℝ≥0} (hglb : ∀ x, (lam : ℝ≥0∞) ≤ g x)
    (a b : ℝ) :
    (lam : ℝ≥0∞) * ENNReal.ofReal (b - a) ≤ (volume.withDensity g) (Icc a b) := by
  rw [withDensity_apply _ measurableSet_Icc]
  calc (lam : ℝ≥0∞) * ENNReal.ofReal (b - a) = (lam : ℝ≥0∞) * volume (Icc a b) := by
        rw [Real.volume_Icc]
    _ = ∫⁻ _ in Icc a b, (lam : ℝ≥0∞) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ t in Icc a b, g t := lintegral_mono fun t => hglb t

/-- A measure with a density with respect to Lebesgue measure has no atoms. -/
theorem withDensity_singleton (g : ℝ → ℝ≥0∞) (a : ℝ) :
    (volume.withDensity g) {a} = 0 := by
  rw [withDensity_apply _ (measurableSet_singleton a)]
  exact setLIntegral_measure_zero _ _ (by simp)

/-- For a monotone map, the preimage of `[T x, T y]` is contained in `[x,y]` together with the
two level sets of the endpoints. -/
theorem preimage_Icc_subset {T : ℝ → ℝ} (hT : Monotone T) (x y : ℝ) :
    T ⁻¹' (Icc (T x) (T y)) ⊆ Icc x y ∪ (T ⁻¹' {T x} ∪ T ⁻¹' {T y}) := by
  intro t ht
  simp only [mem_preimage, mem_Icc] at ht
  rcases le_or_gt x t with h1 | h1
  · rcases le_or_gt t y with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr (by simp [le_antisymm ht.2 (hT h2.le)]))
  · exact Or.inr (Or.inl (by simp [le_antisymm (hT h1.le) ht.1]))

/--
**Regularity of optimal transport maps (Figalli), model case.**

Let `T : ℝ → ℝ` be an optimal transport map for the quadratic cost `c(x,y) = ‖x-y‖²/2`
(which satisfies the Ma–Trudinger–Wang condition `MTW(0)`, see
`Frontier.quadCost_loeperMaxPrinciple`), pushing forward a measure with density `f ≤ Λ`
onto a measure with density `g ≥ λ > 0`.  Optimality is expressed through two-point
`c`-cyclical monotonicity of the graph of `T`, which is the Kantorovich optimality
criterion.  Then `T` is Lipschitz with constant `Λ/λ`; in particular the transport map is
regular, with a quantitative modulus depending only on the density bounds.
-/
theorem figalli_OT_regularity
    {f g : ℝ → ℝ≥0∞} {lam Lam : ℝ≥0} (hlam : 0 < lam)
    (hfub : ∀ x, f x ≤ Lam) (hglb : ∀ y, (lam : ℝ≥0∞) ≤ g y)
    {T : ℝ → ℝ}
    (hopt : ∀ x y : ℝ,
      quadCost x (T x) + quadCost y (T y) ≤ quadCost x (T y) + quadCost y (T x))
    (hpush : Measure.map T (volume.withDensity f) = volume.withDensity g) :
    LipschitzWith (Lam / lam) T := by
  have hTmono : Monotone T := monotone_of_quadCost_cyclMonotone hopt
  have hTmeas : Measurable T := hTmono.measurable
  have hlam0 : (lam : ℝ≥0∞) ≠ 0 := by
    simpa using hlam.ne'
  have hlamtop : (lam : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have key : ∀ x y : ℝ, x ≤ y → T y - T x ≤ ((Lam / lam : ℝ≥0) : ℝ) * (y - x) := by
    intro x y hxy
    have h1 : (lam : ℝ≥0∞) * ENNReal.ofReal (T y - T x)
        ≤ (volume.withDensity g) (Icc (T x) (T y)) := le_withDensity_Icc hglb _ _
    have h2 : (volume.withDensity g) (Icc (T x) (T y))
        = (volume.withDensity f) (T ⁻¹' Icc (T x) (T y)) := by
      rw [← hpush, Measure.map_apply hTmeas measurableSet_Icc]
    have hz : ∀ a : ℝ, (volume.withDensity f) (T ⁻¹' {a}) = 0 := by
      intro a
      have h : (volume.withDensity f) (T ⁻¹' {a}) = (volume.withDensity g) {a} := by
        rw [← hpush, Measure.map_apply hTmeas (measurableSet_singleton a)]
      rw [h, withDensity_singleton]
    have h3 : (volume.withDensity f) (T ⁻¹' Icc (T x) (T y))
        ≤ (volume.withDensity f) (Icc x y) := by
      calc (volume.withDensity f) (T ⁻¹' Icc (T x) (T y))
          ≤ (volume.withDensity f) (Icc x y ∪ (T ⁻¹' {T x} ∪ T ⁻¹' {T y})) :=
            measure_mono (preimage_Icc_subset hTmono x y)
        _ ≤ (volume.withDensity f) (Icc x y)
            + (volume.withDensity f) (T ⁻¹' {T x} ∪ T ⁻¹' {T y}) := measure_union_le _ _
        _ ≤ (volume.withDensity f) (Icc x y)
            + ((volume.withDensity f) (T ⁻¹' {T x})
              + (volume.withDensity f) (T ⁻¹' {T y})) := by
            gcongr
            exact measure_union_le _ _
        _ = (volume.withDensity f) (Icc x y) := by rw [hz, hz]; simp
    have h4 : (volume.withDensity f) (Icc x y) ≤ (Lam : ℝ≥0∞) * ENNReal.ofReal (y - x) :=
      withDensity_Icc_le hfub _ _
    have h5 : (lam : ℝ≥0∞) * ENNReal.ofReal (T y - T x)
        ≤ (lam : ℝ≥0∞) * (((Lam / lam : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (y - x)) := by
      have hcancel : (lam : ℝ≥0∞) * ((Lam / lam : ℝ≥0) : ℝ≥0∞) = (Lam : ℝ≥0∞) := by
        rw [← ENNReal.coe_mul, mul_div_cancel₀ _ hlam.ne']
      rw [← mul_assoc, hcancel]
      exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 h4))
    have h6 : ENNReal.ofReal (T y - T x)
        ≤ ((Lam / lam : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (y - x) :=
      (ENNReal.mul_le_mul_iff_right hlam0 hlamtop).mp h5
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at h6
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by positivity) (by linarith))).mp h6
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rcases le_total x y with h | h
  · rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (T x), abs_sub_comm x,
      abs_of_nonneg (sub_nonneg.mpr (hTmono h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact key x y h
  · rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (hTmono h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact key y x h

/--
A quantitative consequence: under the hypotheses of `Frontier.figalli_OT_regularity`, the
optimal transport map is differentiable at Lebesgue-almost every point, with derivative
bounded by `Λ/λ`.
-/
theorem figalli_OT_regularity_ae_differentiable
    {f g : ℝ → ℝ≥0∞} {lam Lam : ℝ≥0} (hlam : 0 < lam)
    (hfub : ∀ x, f x ≤ Lam) (hglb : ∀ y, (lam : ℝ≥0∞) ≤ g y)
    {T : ℝ → ℝ}
    (hopt : ∀ x y : ℝ,
      quadCost x (T x) + quadCost y (T y) ≤ quadCost x (T y) + quadCost y (T x))
    (hpush : Measure.map T (volume.withDensity f) = volume.withDensity g) :
    (∀ᵐ x ∂(volume : Measure ℝ), DifferentiableAt ℝ T x) ∧
      ∀ x, |deriv T x| ≤ ((Lam / lam : ℝ≥0) : ℝ) := by
  have hL : LipschitzWith (Lam / lam) T := figalli_OT_regularity hlam hfub hglb hopt hpush
  refine ⟨hL.ae_differentiableAt, fun x => ?_⟩
  simpa using norm_deriv_le_of_lipschitz hL (x₀ := x)

/-- The hypotheses of `Frontier.figalli_OT_regularity` are non-vacuous: the identity map is
the optimal map from Lebesgue measure to itself, and the theorem returns the sharp
Lipschitz constant `1`. -/
example : LipschitzWith ((1 : ℝ≥0) / 1) (id : ℝ → ℝ) :=
  figalli_OT_regularity (f := fun _ => 1) (g := fun _ => 1) (lam := 1) (Lam := 1)
    one_pos (fun _ => le_rfl) (fun _ => le_rfl)
    (fun x y => by simp only [quadCost, id, sub_self, norm_zero]; norm_num; positivity)
    (by rw [Measure.map_id])

end Frontier

