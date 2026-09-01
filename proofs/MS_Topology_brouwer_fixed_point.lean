import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/
theorem brouwer_fixed_point {n : ℕ}
    (f : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) → (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hf : Continuous f) : ∃ x, f x = x :=
  Brouwer.brouwer_closedBall f hf

/-- **Banach fixed point theorem** (contraction mapping principle). -/
theorem banach_fixed_point {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    (f : α → α) (K : ℝ) (hK : K < 1) (hf : ∀ x y, dist (f x) (f y) ≤ K * dist x y) :
    ∃! x, f x = x := by
  -- `K` may a priori be negative (only possible when `α` is a subsingleton), so we contract
  -- with the nonnegative constant `max K 0`.
  set K' : NNReal := ⟨max K 0, le_max_right _ _⟩ with hK'
  have hc : ContractingWith K' f := by
    constructor
    · rw [← NNReal.coe_lt_one]
      simp [hK', hK]
    · intro x y
      rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      refine (hf x y).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  exact ⟨hc.fixedPoint f, hc.fixedPoint_isFixedPt, fun y hy => hc.fixedPoint_unique hy⟩

/-- **Pythagorean theorem** in a real inner product space.
(The statement is as given, with the inner product's scalar field made explicit, as required by
the current `inner` notation.) -/
theorem pythagorean {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V)
    (h : inner ℝ x y = (0 : ℝ)) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, h]; ring

/-- A finite connected acyclic graph (a tree) has one fewer edge than it has vertices. -/
theorem euler_char_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hc : G.Connected) (ha : G.IsAcyclic) :
    G.edgeFinset.card + 1 = Fintype.card V :=
  SimpleGraph.IsTree.card_edgeFinset ⟨hc, ha⟩

/-- Placeholder statement as provided in the original file: it is literally `True`, so it carries
no topological content (in particular it is *not* the Jordan curve theorem). -/
theorem jordan_curve_no_separation : True := trivial

end MS.Topology

import Mathlib

/-!
# Brouwer's fixed point theorem

A complete proof of Brouwer's fixed point theorem for the closed unit ball of a finite
dimensional real inner product space, following the analytic proof of Milnor:

* a `C¹` retraction of the ball onto its boundary sphere cannot exist, because the volume of the
  image of the ball under `x ↦ x + t (r x - x)` is simultaneously a polynomial in `t`, constant
  equal to the volume of the ball for small `t`, and zero at `t = 1`;
* a continuous fixed point free self map of the ball can be approximated (Stone–Weierstrass) by a
  smooth fixed point free self map, from which such a retraction is built by shooting a ray from
  the image point through the source point to the sphere.
-/

open Metric Set MeasureTheory Module
open scoped ENNReal NNReal RealInnerProductSpace

namespace Brouwer

/-! ### The determinant of `id + t A` as a polynomial in `t` -/

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient functions appearing in the expansion of `det (id + t A)`. -/
noncomputable def coef (b : Basis ι ℝ E) (σ : Equiv.Perm ι) (S : Finset ι) (A : E →L[ℝ] E) : ℝ :=
  (Equiv.Perm.sign σ : ℝ) * (∏ i ∈ S, if σ i = i then (1 : ℝ) else 0) *
    ∏ i ∈ Finset.univ \ S, LinearMap.toMatrix b b (A : E →ₗ[ℝ] E) (σ i) i

lemma continuous_coef (b : Basis ι ℝ E) (σ : Equiv.Perm ι) (S : Finset ι) :
    Continuous (coef b σ S) := by
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
  refine Continuous.mul continuous_const (continuous_finset_prod _ fun i _ => ?_)
  simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
  have h1 : Continuous fun w : E => b.repr w (σ i) :=
    LinearMap.continuous_of_finiteDimensional ((Finsupp.lapply (σ i)).comp b.repr.toLinearMap)
  exact h1.comp ((ContinuousLinearMap.apply ℝ E (b i)).continuous)

/-- Expansion of `det (id + t • A)` as a polynomial expression in `t`. -/
lemma det_id_add_smul_eq (b : Basis ι ℝ E) (A : E →L[ℝ] E) (t : ℝ) :
    (ContinuousLinearMap.id ℝ E + t • A).det =
      ∑ p ∈ (Finset.univ : Finset (Equiv.Perm ι × Finset ι)),
        t ^ (Finset.univ \ p.2).card * coef b p.1 p.2 A := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) : E →ₗ[ℝ] E)
      = 1 + t • LinearMap.toMatrix b b (A : E →ₗ[ℝ] E) := by
    simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul,
      ContinuousLinearMap.coe_id, map_add, map_smul, LinearMap.toMatrix_id]
  rw [hM, Matrix.det_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 : ∀ i : ι, ((1 : Matrix ι ι ℝ) + t • LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)) (σ i) i
      = (if σ i = i then (1 : ℝ) else 0)
          + t * LinearMap.toMatrix b b (A : E →ₗ[ℝ] E) (σ i) i := by
    intro i; simp [Matrix.one_apply]
  simp only [h1]
  rw [Finset.prod_add, Finset.smul_sum, ← Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp [coef, Finset.prod_mul_distrib, Units.smul_def]
  ring

end Det

/-! ### Positivity and nonvanishing of `det (id + t A)` -/

section DetPos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma det_id_add_smul_ne_zero (A : E →L[ℝ] E) {t : ℝ} (h : ‖t • A‖ < 1) :
    (ContinuousLinearMap.id ℝ E + t • A).det ≠ 0 := by
  rw [ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_ne_iff,
    LinearMap.ker_eq_bot']
  intro y hy
  by_contra hy0
  have h1 : y + (t • A) y = 0 := by simpa using hy
  have h3 : (t • A) y = -y := by linear_combination (norm := module) h1
  have h2 : ‖y‖ ≤ ‖t • A‖ * ‖y‖ := by
    calc ‖y‖ = ‖(t • A) y‖ := by rw [h3, norm_neg]
    _ ≤ ‖t • A‖ * ‖y‖ := (t • A).le_opNorm y
  have := norm_pos_iff.mpr hy0
  nlinarith

lemma continuous_det_id_add_smul (A : E →L[ℝ] E) :
    Continuous fun t : ℝ => (ContinuousLinearMap.id ℝ E + t • A).det := by
  simp only [fun t : ℝ => det_id_add_smul_eq (Module.finBasis ℝ E) A t]
  exact continuous_finset_sum _ fun p _ => (continuous_pow _).mul continuous_const

lemma det_id_add_smul_pos (A : E →L[ℝ] E) {t : ℝ} (ht : 0 ≤ t) (h : t * ‖A‖ < 1) :
    0 < (ContinuousLinearMap.id ℝ E + t • A).det := by
  by_contra hle
  push_neg at hle
  have hF0 : (ContinuousLinearMap.id ℝ E + (0 : ℝ) • A).det = 1 := by
    simp [ContinuousLinearMap.det]
  have hmem : (0 : ℝ) ∈ (fun s : ℝ => (ContinuousLinearMap.id ℝ E + s • A).det) '' (Icc 0 t) := by
    refine intermediate_value_Icc' ht (continuous_det_id_add_smul A).continuousOn ?_
    rw [mem_Icc]
    exact ⟨hle, by rw [hF0]; norm_num⟩
  obtain ⟨s, hs, hFs⟩ := hmem
  refine det_id_add_smul_ne_zero A ?_ hFs
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  have hs0 : 0 ≤ s := hs.1
  have : ‖s • A‖ = s * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  rw [this]
  nlinarith [hs.2]

/-- If `‖t • A‖ < 1` then `id + t • A` is a linear homeomorphism. -/
lemma exists_equiv_id_add_smul (A : E →L[ℝ] E) {t : ℝ} (h : ‖t • A‖ < 1) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E + t • A := by
  have hinj : Function.Injective
      ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    have h1 : y + (t • A) y = 0 := by simpa using hy
    have h3 : (t • A) y = -y := by linear_combination (norm := module) h1
    have h2 : ‖y‖ ≤ ‖t • A‖ * ‖y‖ := by
      calc ‖y‖ = ‖(t • A) y‖ := by rw [h3, norm_neg]
      _ ≤ ‖t • A‖ * ‖y‖ := (t • A).le_opNorm y
    have := norm_pos_iff.mpr hy0
    nlinarith
  have hbij : Function.Bijective
      ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  refine ⟨(LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv, ?_⟩
  ext y
  rfl

lemma continuousOn_det_id_add_smul {s : Set E} {A : E → E →L[ℝ] E} (hA : ContinuousOn A s)
    (t : ℝ) : ContinuousOn (fun x => (ContinuousLinearMap.id ℝ E + t • A x).det) s := by
  simp only [fun x => det_id_add_smul_eq (Module.finBasis ℝ E) (A x) t]
  exact continuousOn_finset_sum _ fun p _ =>
    continuousOn_const.mul ((continuous_coef _ p.1 p.2).comp_continuousOn hA)

end DetPos

/-! ### The volume integral is a polynomial in `t` -/

section Poly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma exists_polynomial_integral_det (A : E → (E →L[ℝ] E))
    (hA : ContinuousOn A (closedBall 0 1)) :
    ∃ q : Polynomial ℝ, ∀ t : ℝ,
      q.eval t = ∫ x in ball (0 : E) 1, (ContinuousLinearMap.id ℝ E + t • A x).det
        ∂(Measure.addHaar : Measure E) := by
  classical
  set μ : Measure E := Measure.addHaar
  set b := Module.finBasis ℝ E with hb
  have hint : ∀ (σ : Equiv.Perm (Fin (finrank ℝ E))) (S : Finset (Fin (finrank ℝ E))),
      IntegrableOn (fun x => coef b σ S (A x)) (ball (0 : E) 1) μ := by
    intro σ S
    have hc : ContinuousOn (fun x => coef b σ S (A x)) (closedBall (0 : E) 1) :=
      (continuous_coef b σ S).comp_continuousOn hA
    exact (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  refine ⟨∑ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin (finrank ℝ E)) ×
      Finset (Fin (finrank ℝ E)))),
      Polynomial.C (∫ x in ball (0 : E) 1, coef b p.1 p.2 (A x) ∂μ) *
        Polynomial.X ^ ((Finset.univ \ p.2).card), fun t => ?_⟩
  rw [Polynomial.eval_finset_sum]
  have key : ∀ x, (ContinuousLinearMap.id ℝ E + t • A x).det
      = ∑ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin (finrank ℝ E)) ×
          Finset (Fin (finrank ℝ E)))),
        t ^ (Finset.univ \ p.2).card * coef b p.1 p.2 (A x) := fun x => det_id_add_smul_eq b (A x) t
  simp only [key]
  rw [integral_finset_sum _ (fun p _ => (hint p.1 p.2).const_mul _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

end Poly

/-! ### No `C¹` retraction of the ball onto the sphere -/

section NoRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `r` has constant norm `1` near `x`, the determinant of its derivative at `x` vanishes. -/
lemma det_fderiv_eq_zero_of_norm_eq_one {r : E → E} {x : E} {s : Set E} (hs : IsOpen s)
    (hx : x ∈ s) (hd : DifferentiableAt ℝ r x) (hn : ∀ y ∈ s, ‖r y‖ = 1) :
    (fderiv ℝ r x).det = 0 := by
  have hge : (fun y => ⟪r y, r y⟫) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [real_inner_self_eq_norm_sq, hn y hy]; norm_num
  have h0 : fderiv ℝ (fun y => ⟪r y, r y⟫) x = 0 := by rw [hge.fderiv_eq]; simp
  have hperp : ∀ y : E, ⟪r x, fderiv ℝ r x y⟫ = 0 := by
    intro y
    have h1 := fderiv_inner_apply (𝕜 := ℝ) hd hd y
    rw [h0] at h1
    simp only [ContinuousLinearMap.zero_apply] at h1
    have hc := real_inner_comm (r x) (fderiv ℝ r x y)
    linarith
  have hrx : ‖r x‖ = 1 := hn x hx
  rw [ContinuousLinearMap.det]
  by_contra hdet
  have hinj : Function.Injective ((fderiv ℝ r x : E →ₗ[ℝ] E)) := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) (r x)
  have h2 := hperp y
  rw [show fderiv ℝ r x y = r x from hy, real_inner_self_eq_norm_sq, hrx] at h2
  norm_num at h2

set_option maxHeartbeats 2000000 in
/-- **No retraction theorem** (`C¹` version): there is no continuously differentiable map from
a neighbourhood of the closed unit ball to the unit sphere which is the identity on the sphere. -/
theorem no_smooth_retraction {U : Set E} (hU : IsOpen U) (hsub : closedBall (0 : E) 1 ⊆ U)
    {r : E → E} (hr : ContDiffOn ℝ 1 r U)
    (hnorm : ∀ x ∈ closedBall (0 : E) 1, ‖r x‖ = 1)
    (hfix : ∀ x ∈ sphere (0 : E) 1, r x = x) : False := by
  classical
  set μ : Measure E := Measure.addHaar with hμ
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ r x := fun x hx =>
    ((hr.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)
  set V : E → (E →L[ℝ] E) := fun x => fderiv ℝ r x - ContinuousLinearMap.id ℝ E with hVdef
  have hVcont : ContinuousOn V U :=
    (hr.continuousOn_fderiv_of_isOpen hU le_rfl).sub continuousOn_const
  have hVcb : ContinuousOn V (closedBall (0 : E) 1) := hVcont.mono hsub
  have hvderiv : ∀ x ∈ U, HasFDerivAt (fun y => r y - y) (V x) x := fun x hx => by
    simpa [hVdef] using ((hdiff x hx).hasFDerivAt.sub (hasFDerivAt_id x))
  obtain ⟨L0, hL0⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn hVcb
  set L : ℝ := max L0 1 with hLdef
  have hL1 : (1 : ℝ) ≤ L := le_max_right _ _
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  have hL : ∀ x ∈ closedBall (0 : E) 1, ‖V x‖ ≤ L := fun x hx => (hL0 x hx).trans (le_max_left _ _)
  set t₀ : ℝ := 1 / (2 * L) with ht₀def
  have ht₀pos : 0 < t₀ := by rw [ht₀def]; positivity
  have ht₀half : t₀ * L = 1 / 2 := by rw [ht₀def]; field_simp
  have ht₀le : t₀ ≤ 1 / 2 := by
    rw [ht₀def]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  -- The key computation: for small `t` the map `x ↦ x + t (r x - x)` preserves the ball.
  have key : ∀ t ∈ Icc (0 : ℝ) t₀,
      ∫ x in ball (0 : E) 1, (ContinuousLinearMap.id ℝ E + t • V x).det ∂μ
        = (μ (ball (0 : E) 1)).toReal := by
    rintro t ⟨ht0, htt₀⟩
    have htle : t ≤ 1 / 2 := htt₀.trans ht₀le
    have htL' : t * L ≤ 1 / 2 := by
      calc t * L ≤ t₀ * L := by nlinarith
        _ = 1 / 2 := ht₀half
    have htL : ∀ x ∈ closedBall (0 : E) 1, t * ‖V x‖ ≤ 1 / 2 := by
      intro x hx
      have := hL x hx
      nlinarith [norm_nonneg (V x)]
    have hsmul : ∀ x ∈ closedBall (0 : E) 1, ‖t • V x‖ < 1 := by
      intro x hx
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      linarith [htL x hx]
    set f : E → E := fun x => x + t • (r x - x) with hfdef
    have hfd : ∀ x ∈ U, HasFDerivAt f (ContinuousLinearMap.id ℝ E + t • V x) x := fun x hx =>
      (hasFDerivAt_id x).add ((hvderiv x hx).const_smul t)
    have hfcont : ContinuousOn f (closedBall (0 : E) 1) := fun x hx =>
      ((hfd x (hsub hx)).continuousAt).continuousWithinAt
    have hfball : ∀ x ∈ ball (0 : E) 1, f x ∈ ball (0 : E) 1 := by
      intro x hx
      have hx1 : ‖x‖ < 1 := by simpa using hx
      have hrx : ‖r x‖ = 1 := hnorm x (ball_subset_closedBall hx)
      have hfx : f x = (1 - t) • x + t • r x := by rw [hfdef]; module
      rw [mem_ball_zero_iff, hfx]
      calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * 1 := by
            rw [norm_smul, norm_smul, hrx, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), abs_of_nonneg ht0]
        _ < 1 := by nlinarith
    have hsph : ∀ x ∈ sphere (0 : E) 1, f x = x := by
      intro x hx; rw [hfdef]; simp [hfix x hx]
    -- injectivity
    have hlip : LipschitzOnWith (Real.toNNReal L) (fun y => r y - y) (closedBall (0 : E) 1) := by
      refine (convex_closedBall (0 : E) 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
        (fun x hx => (hvderiv x (hsub hx)).hasFDerivWithinAt) ?_
      intro x hx
      have : (‖V x‖₊ : ℝ) ≤ ((Real.toNNReal L : ℝ≥0) : ℝ) := by
        rw [Real.coe_toNNReal _ hLpos.le]
        exact hL x hx
      exact_mod_cast this
    have hinj : InjOn f (closedBall (0 : E) 1) := by
      intro x hx y hy hxy
      have h1 : ‖(r x - x) - (r y - y)‖ ≤ L * ‖x - y‖ := by
        have h := hlip.dist_le_mul x hx y hy
        rw [dist_eq_norm, dist_eq_norm] at h
        simpa [Real.coe_toNNReal _ hLpos.le] using h
      have h2 : x - y = -(t • ((r x - x) - (r y - y))) := by
        have h3 : f x - f y = 0 := by rw [hxy]; simp
        rw [hfdef] at h3
        simp only at h3
        linear_combination (norm := module) h3
      have h4 : ‖x - y‖ ≤ t * (L * ‖x - y‖) :=
        calc ‖x - y‖ = t * ‖(r x - x) - (r y - y)‖ := by
              conv_lhs => rw [h2]
              rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
          _ ≤ t * (L * ‖x - y‖) := mul_le_mul_of_nonneg_left h1 ht0
      have h5 : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h5)
    -- `f` is an open map on the ball
    have hopenim : IsOpen (f '' (ball (0 : E) 1)) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨x, hx, rfl⟩
      have hxU : x ∈ U := hsub (ball_subset_closedBall hx)
      obtain ⟨e, he⟩ := exists_equiv_id_add_smul (V x) (hsmul x (ball_subset_closedBall hx))
      have hcd : ContDiffAt ℝ 1 f x := by
        have hcr : ContDiffAt ℝ 1 r x := hr.contDiffAt (hU.mem_nhds hxU)
        exact contDiffAt_id.add (contDiffAt_const.smul (hcr.sub contDiffAt_id))
      have hstrict : HasStrictFDerivAt f (e : E →L[ℝ] E) x := by
        rw [he, ← (hfd x hxU).fderiv]
        exact hcd.hasStrictFDerivAt one_ne_zero
      rw [← hstrict.map_nhds_eq_of_equiv]
      exact Filter.image_mem_map (isOpen_ball.mem_nhds hx)
    have hclosedim : IsClosed (f '' (closedBall (0 : E) 1)) :=
      ((isCompact_closedBall (0 : E) 1).image_of_continuousOn hfcont).isClosed
    -- points of the ball in the image of the closed ball come from the open ball
    have hfromball : ∀ z ∈ ball (0 : E) 1, z ∈ f '' (closedBall (0 : E) 1) →
        z ∈ f '' (ball (0 : E) 1) := by
      rintro z hz ⟨x, hx, rfl⟩
      rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hx) with h | h
      · exact ⟨x, mem_ball_zero_iff.mpr h, rfl⟩
      · exfalso
        have hxs : x ∈ sphere (0 : E) 1 := by simp [h]
        rw [hsph x hxs, mem_ball_zero_iff, h] at hz
        exact lt_irrefl _ hz
    have himage : f '' (ball (0 : E) 1) = ball (0 : E) 1 := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩; exact hfball x hx
      · intro y hy
        by_contra hyn
        have hyC : y ∉ f '' (closedBall (0 : E) 1) := fun h => hyn (hfromball y hy h)
        have hpre : IsPreconnected (ball (0 : E) 1) := (convex_ball (0 : E) 1).isPreconnected
        have hcover : ball (0 : E) 1 ⊆
            f '' (ball (0 : E) 1) ∪ (f '' (closedBall (0 : E) 1))ᶜ := by
          intro z hz
          by_cases hzc : z ∈ f '' (closedBall (0 : E) 1)
          · exact Or.inl (hfromball z hz hzc)
          · exact Or.inr hzc
        obtain ⟨w, _, hw2, hw3⟩ := hpre _ _ hopenim hclosedim.isOpen_compl hcover
          ⟨f 0, hfball 0 (mem_ball_self one_pos), ⟨0, mem_ball_self one_pos, rfl⟩⟩ ⟨y, hy, hyC⟩
        obtain ⟨x, hx, hxw⟩ := hw2
        exact hw3 ⟨x, ball_subset_closedBall hx, hxw⟩
    -- change of variables
    have hdetpos : ∀ x ∈ ball (0 : E) 1,
        0 < (ContinuousLinearMap.id ℝ E + t • V x).det := fun x hx =>
      det_id_add_smul_pos (V x) ht0 (by linarith [htL x (ball_subset_closedBall hx)])
    have hcv : ∫⁻ x in ball (0 : E) 1,
        ENNReal.ofReal |(ContinuousLinearMap.id ℝ E + t • V x).det| ∂μ = μ (ball (0 : E) 1) := by
      conv_rhs => rw [← himage]
      exact lintegral_abs_det_fderiv_eq_addHaar_image μ measurableSet_ball
        (fun x hx => (hfd x (hsub (ball_subset_closedBall hx))).hasFDerivWithinAt)
        (hinj.mono ball_subset_closedBall)
    have hintg : IntegrableOn
        (fun x => (ContinuousLinearMap.id ℝ E + t • V x).det) (ball (0 : E) 1) μ :=
      (((continuousOn_det_id_add_smul hVcb t).integrableOn_compact
        (isCompact_closedBall _ _))).mono_set ball_subset_closedBall
    have hnonneg : 0 ≤ᵐ[μ.restrict (ball (0 : E) 1)]
        fun x => (ContinuousLinearMap.id ℝ E + t • V x).det := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx using (hdetpos x hx).le
    rw [setLIntegral_congr_fun measurableSet_ball
      (fun x hx => by rw [abs_of_pos (hdetpos x hx)]),
      ← ofReal_integral_eq_lintegral_ofReal hintg hnonneg] at hcv
    rw [← hcv, ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)]
  -- the integral is a polynomial in `t`, constant on `[0, t₀]`, hence constant
  obtain ⟨q, hq⟩ := exists_polynomial_integral_det V hVcb
  set c : ℝ := (μ (ball (0 : E) 1)).toReal with hcdef
  have hsubroot : Icc (0 : ℝ) t₀ ⊆ {x | (q - Polynomial.C c).IsRoot x} := by
    intro t ht
    simp only [mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C,
      sub_eq_zero]
    rw [hq t]
    exact key t ht
  have hroots : q - Polynomial.C c = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.Infinite.mono hsubroot (Set.Icc_infinite ht₀pos))
  have hq1 : q.eval 1 = c := by
    have h := congrArg (Polynomial.eval 1) hroots
    simpa [sub_eq_zero] using h
  have hzero : q.eval 1 = 0 := by
    rw [hq 1]
    have hz : ∀ x ∈ ball (0 : E) 1,
        (ContinuousLinearMap.id ℝ E + (1 : ℝ) • V x).det = 0 := by
      intro x hx
      have hEq : ContinuousLinearMap.id ℝ E + (1 : ℝ) • V x = fderiv ℝ r x := by
        simp [hVdef]
      rw [hEq]
      exact det_fderiv_eq_zero_of_norm_eq_one isOpen_ball hx
        (hdiff x (hsub (ball_subset_closedBall hx)))
        (fun y hy => hnorm y (ball_subset_closedBall hy))
    rw [setIntegral_congr_fun measurableSet_ball hz]
    simp
  have hcpos : 0 < c :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  linarith

end NoRetraction

/-! ### Smooth approximation of continuous functions on a compact set -/

section Approx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Real valued Stone–Weierstrass: continuous functions on a compact subset of `E` are uniformly
approximated by restrictions of globally `C¹` functions. -/
lemma exists_contDiff_approx_real {K : Set E} (hK : IsCompact K) (φ : E → ℝ)
    (hφ : ContinuousOn φ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E → ℝ, ContDiff ℝ 1 G ∧ ∀ x ∈ K, |G x - φ x| < ε := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set fK : C(K, ℝ) := ⟨K.restrict φ, hφ.restrict⟩ with hfK
  set A : Subalgebra ℝ C(K, ℝ) :=
  { carrier := {g : C(K, ℝ) | ∃ G : E → ℝ, ContDiff ℝ 1 G ∧ ∀ x : K, g x = G x}
    mul_mem' := by
      rintro g h ⟨G, hG, hGg⟩ ⟨H, hH, hHh⟩
      exact ⟨fun v => G v * H v, hG.mul hH, fun x => by simp [hGg x, hHh x]⟩
    add_mem' := by
      rintro g h ⟨G, hG, hGg⟩ ⟨H, hH, hHh⟩
      exact ⟨fun v => G v + H v, hG.add hH, fun x => by simp [hGg x, hHh x]⟩
    zero_mem' := ⟨fun _ => 0, contDiff_const, fun _ => rfl⟩
    one_mem' := ⟨fun _ => 1, contDiff_const, fun _ => rfl⟩
    algebraMap_mem' := fun c => ⟨fun _ => c, contDiff_const, fun _ => rfl⟩ } with hA
  have hsep : A.SeparatesPoints := by
    rintro x y hxy
    have hne : (x : E) - (y : E) ≠ 0 := sub_ne_zero.mpr (fun h => hxy (Subtype.ext h))
    let g : C(K, ℝ) := ⟨fun z : K => ⟪(x : E) - (y : E), (z : E)⟫,
      continuous_const.inner continuous_subtype_val⟩
    have hgA : g ∈ A := ⟨fun v => ⟪(x : E) - (y : E), v⟫,
      (innerSL ℝ ((x : E) - (y : E))).contDiff, fun _ => rfl⟩
    refine ⟨⇑g, ⟨g, hgA, rfl⟩, ?_⟩
    intro h
    apply hne
    have h2 : ⟪(x : E) - (y : E), (x : E) - (y : E)⟫ = 0 := by
      rw [inner_sub_right]
      have hxy' : ⟪(x : E) - (y : E), (x : E)⟫ = ⟪(x : E) - (y : E), (y : E)⟫ := h
      linarith
    exact inner_self_eq_zero.mp h2
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hmem : fK ∈ closure (A : Set C(K, ℝ)) := by
    have hmem' : fK ∈ A.topologicalClosure := by rw [htop]; trivial
    exact hmem'
  obtain ⟨g, hgA, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨G, hG, hGg⟩ := hgA
  refine ⟨G, hG, fun x hx => ?_⟩
  have h1 : dist (fK ⟨x, hx⟩) (g ⟨x, hx⟩) ≤ dist fK g := ContinuousMap.dist_apply_le_dist _
  rw [Real.dist_eq] at h1
  have h2 : g ⟨x, hx⟩ = G x := hGg ⟨x, hx⟩
  have h3 : fK ⟨x, hx⟩ = φ x := rfl
  rw [h2, h3] at h1
  rw [abs_sub_comm]
  linarith

/-- Vector valued version of `exists_contDiff_approx_real`. -/
lemma exists_contDiff_approx {K : Set E} (hK : IsCompact K) (φ : E → E)
    (hφ : ContinuousOn φ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E → E, ContDiff ℝ 1 G ∧ ∀ x ∈ K, ‖G x - φ x‖ < ε := by
  classical
  set d := finrank ℝ E with hd
  set bb := stdOrthonormalBasis ℝ E with hbb
  set ε' : ℝ := ε / (d + 1) with hε'
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  have hcoord : ∀ i : Fin d, ∃ Gi : E → ℝ, ContDiff ℝ 1 Gi ∧
      ∀ x ∈ K, |Gi x - ⟪bb i, φ x⟫| < ε' := fun i =>
    exists_contDiff_approx_real hK (fun v => ⟪bb i, φ v⟫) (continuousOn_const.inner hφ) hε'pos
  choose G hG1 hG2 using hcoord
  refine ⟨fun v => ∑ i, G i v • bb i, ContDiff.sum fun i _ => (hG1 i).smul contDiff_const, ?_⟩
  intro x hx
  have hrep : φ x = ∑ i, ⟪bb i, φ x⟫ • bb i := by
    conv_lhs => rw [← bb.sum_repr (φ x)]
    exact Finset.sum_congr rfl fun i _ => by rw [bb.repr_apply_apply]
  have hdiff : (∑ i, G i x • bb i) - φ x = ∑ i, (G i x - ⟪bb i, φ x⟫) • bb i := by
    conv_lhs => rw [hrep]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [sub_smul]
  rw [hdiff]
  calc ‖∑ i, (G i x - ⟪bb i, φ x⟫) • bb i‖ ≤ ∑ i, ‖(G i x - ⟪bb i, φ x⟫) • bb i‖ :=
        norm_sum_le _ _
    _ = ∑ i : Fin d, |G i x - ⟪bb i, φ x⟫| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, bb.norm_eq_one i, Real.norm_eq_abs, mul_one]
    _ ≤ ∑ _i : Fin d, ε' := Finset.sum_le_sum fun i _ => (hG2 i x hx).le
    _ = d * ε' := by simp
    _ < ε := by
        rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [Nat.cast_nonneg (α := ℝ) d]

end Approx

/-! ### Brouwer's fixed point theorem -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Shooting the ray from `x` in the direction `u` hits the unit sphere: the resulting point has
norm one. -/
lemma norm_ray_eq_one {x u : E}
    (hD : 0 ≤ ⟪x, u⟫ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2)) (hu : u ≠ 0) :
    ‖x + ((-⟪x, u⟫ + Real.sqrt (⟪x, u⟫ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2))) / ‖u‖ ^ 2) • u‖ = 1 := by
  set A := ⟪x, u⟫ with hA
  set Nn := ‖u‖ ^ 2 with hNn
  set Dd := A ^ 2 + Nn * (1 - ‖x‖ ^ 2) with hDd
  have hNpos : 0 < Nn := by rw [hNn]; positivity
  set S := (-A + Real.sqrt Dd) / Nn with hS
  have hsq : Real.sqrt Dd ^ 2 = Dd := Real.sq_sqrt hD
  have h1 : ‖x + S • u‖ ^ 2 = ‖x‖ ^ 2 + 2 * (S * A) + S ^ 2 * Nn := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← hA, ← hNn]
  have h2 : ‖x‖ ^ 2 + 2 * (S * A) + S ^ 2 * Nn = 1 := by
    rw [hS]; field_simp; linear_combination hsq + hDd
  have h3 : ‖x + S • u‖ ^ 2 = 1 := by rw [h1, h2]
  have h4 : (‖x + S • u‖ - 1) * (‖x + S • u‖ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h4 with h | h
  · linarith
  · linarith [norm_nonneg (x + S • u)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `x` already lies on the unit sphere and points away from `u`, the ray does not move it. -/
lemma ray_coeff_eq_zero {x u : E} (hx : ‖x‖ = 1) (ha : 0 < ⟪x, u⟫) :
    ((-⟪x, u⟫ + Real.sqrt (⟪x, u⟫ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2))) / ‖u‖ ^ 2) = 0 := by
  have h0 : (1 : ℝ) - ‖x‖ ^ 2 = 0 := by rw [hx]; norm_num
  rw [h0, mul_zero, add_zero, Real.sqrt_sq ha.le, neg_add_cancel, zero_div]

/-- A `C¹` self map of the closed unit ball has a fixed point. -/
theorem exists_fixedPoint_of_contDiff {g : E → E} (hg : ContDiff ℝ 1 g)
    (hmaps : ∀ x ∈ closedBall (0 : E) 1, ‖g x‖ ≤ 1) :
    ∃ x ∈ closedBall (0 : E) 1, g x = x := by
  by_contra hcon
  push_neg at hcon
  set u : E → E := fun x => x - g x with hudef
  have hucd : ContDiff ℝ 1 u := contDiff_id.sub hg
  set A : E → ℝ := fun x => ⟪x, u x⟫ with hAdef
  set D : E → ℝ := fun x => A x ^ 2 + ‖u x‖ ^ 2 * (1 - ‖x‖ ^ 2) with hDdef
  have hAcd : ContDiff ℝ 1 A := contDiff_id.inner ℝ hucd
  have hDcd : ContDiff ℝ 1 D :=
    (hAcd.pow 2).add ((hucd.norm_sq ℝ).mul (contDiff_const.sub (contDiff_id.norm_sq ℝ)))
  set S : E → ℝ := fun x => (-A x + Real.sqrt (D x)) / ‖u x‖ ^ 2 with hSdef
  set r : E → E := fun x => x + S x • u x with hrdef
  set U : Set E := {x | u x ≠ 0 ∧ 0 < D x} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_ne_fun hucd.continuous continuous_const).inter
      (isOpen_lt continuous_const hDcd.continuous)
  have hApos : ∀ x ∈ sphere (0 : E) 1, 0 < A x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by simpa using hx
    by_contra hle
    push_neg at hle
    have hAx : A x = ‖x‖ ^ 2 - ⟪x, g x⟫ := by
      rw [hAdef]; simp [hudef, inner_sub_right]
    rw [hAx, hx1] at hle
    have hgx : ‖g x‖ ≤ 1 := hmaps x (by simp [hx1])
    have hz : ‖g x - x‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, hx1]
      nlinarith [real_inner_comm x (g x), norm_nonneg (g x)]
    have h0 : ‖g x - x‖ = 0 := by nlinarith [norm_nonneg (g x - x)]
    exact hcon x (by simp [hx1]) (sub_eq_zero.mp (norm_eq_zero.mp h0))
  have hsub : closedBall (0 : E) 1 ⊆ U := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    have hune : u x ≠ 0 := fun h => hcon x hx (sub_eq_zero.mp h).symm
    refine ⟨hune, ?_⟩
    show 0 < A x ^ 2 + ‖u x‖ ^ 2 * (1 - ‖x‖ ^ 2)
    rcases lt_or_eq_of_le hx1 with h | h
    · have h1 : 0 < ‖u x‖ ^ 2 := by positivity
      have h2 : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      nlinarith [sq_nonneg (A x)]
    · have h0 : (1 : ℝ) - ‖x‖ ^ 2 = 0 := by rw [h]; norm_num
      rw [h0, mul_zero, add_zero]
      exact pow_pos (hApos x (mem_sphere_zero_iff_norm.mpr h)) 2
  have hrcd : ContDiffOn ℝ 1 r U := by
    intro x hx
    have hsqrt : ContDiffAt ℝ 1 (fun y => Real.sqrt (D y)) x :=
      (Real.contDiffAt_sqrt (ne_of_gt hx.2)).comp x hDcd.contDiffAt
    have hnu : ‖u x‖ ^ 2 ≠ 0 := by
      have : u x ≠ 0 := hx.1
      positivity
    have hScd : ContDiffAt ℝ 1 S x :=
      ContDiffAt.div (hAcd.contDiffAt.neg.add hsqrt) (hucd.norm_sq ℝ).contDiffAt hnu
    exact (contDiffAt_id.add (hScd.smul hucd.contDiffAt)).contDiffWithinAt
  have hnorm : ∀ x ∈ closedBall (0 : E) 1, ‖r x‖ = 1 := fun x hx =>
    norm_ray_eq_one (hsub hx).2.le (hsub hx).1
  have hfix : ∀ x ∈ sphere (0 : E) 1, r x = x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by simpa using hx
    have hS0 : S x = 0 := ray_coeff_eq_zero hx1 (hApos x hx)
    show x + S x • u x = x
    rw [hS0, zero_smul, add_zero]
  exact no_smooth_retraction hUopen hsub hrcd hnorm hfix

/-- **Brouwer's fixed point theorem** for the closed unit ball of a finite dimensional real
inner product space. -/
theorem brouwer_closedBall (f : closedBall (0 : E) 1 → closedBall (0 : E) 1)
    (hf : Continuous f) : ∃ x, f x = x := by
  classical
  by_contra hcon
  push_neg at hcon
  have hKc : IsCompact (closedBall (0 : E) 1) := isCompact_closedBall _ _
  set φ : E → E := fun x => if hx : x ∈ closedBall (0 : E) 1 then (f ⟨x, hx⟩ : E) else 0 with hφdef
  have hφval : ∀ (x : E) (hx : x ∈ closedBall (0 : E) 1), φ x = (f ⟨x, hx⟩ : E) := by
    intro x hx; rw [hφdef]; simp only [dif_pos hx]
  have hres : (closedBall (0 : E) 1).restrict φ = fun x : closedBall (0 : E) 1 => (f x : E) := by
    funext x
    simp only [Set.restrict_apply, hφval x x.2, Subtype.coe_eta]
  have hφc : ContinuousOn φ (closedBall (0 : E) 1) := by
    rw [continuousOn_iff_continuous_restrict, hres]
    exact continuous_subtype_val.comp hf
  have hφmem : ∀ x ∈ closedBall (0 : E) 1, ‖φ x‖ ≤ 1 := by
    intro x hx
    rw [hφval x hx]
    exact mem_closedBall_zero_iff.mp (f ⟨x, hx⟩).2
  have hne : ∀ x ∈ closedBall (0 : E) 1, φ x ≠ x := by
    intro x hx h
    exact hcon ⟨x, hx⟩ (Subtype.ext ((hφval x hx).symm.trans h))
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hKc.exists_isMinOn ⟨0, by simp⟩ ((hφc.sub continuousOn_id).norm)
  set ε : ℝ := ‖φ x₀ - x₀‖ with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef, norm_pos_iff, sub_ne_zero]
    exact hne x₀ hx₀K
  have hlow : ∀ x ∈ closedBall (0 : E) 1, ε ≤ ‖φ x - x‖ := fun x hx => hx₀min hx
  set δ : ℝ := ε / 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨G, hG, hGapp⟩ := exists_contDiff_approx hKc φ hφc hδpos
  set c : ℝ := (1 + δ)⁻¹ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  set g : E → E := fun x => c • G x with hgdef
  have hgcd : ContDiff ℝ 1 g := contDiff_const.smul hG
  have hGb : ∀ x ∈ closedBall (0 : E) 1, ‖G x‖ ≤ 1 + δ := by
    intro x hx
    have hsplit : G x = φ x + (G x - φ x) := by abel
    calc ‖G x‖ = ‖φ x + (G x - φ x)‖ := by rw [← hsplit]
      _ ≤ ‖φ x‖ + ‖G x - φ x‖ := norm_add_le _ _
      _ ≤ 1 + δ := by linarith [hφmem x hx, hGapp x hx]
  have hgmaps : ∀ x ∈ closedBall (0 : E) 1, ‖g x‖ ≤ 1 := by
    intro x hx
    have h1 : ‖g x‖ = c * ‖G x‖ := by
      rw [hgdef]; simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [h1, hcdef, inv_mul_eq_div, div_le_one (by linarith)]
    exact hGb x hx
  have hgapp : ∀ x ∈ closedBall (0 : E) 1, ‖g x - φ x‖ < 2 * δ := by
    intro x hx
    have h1 : ‖g x - G x‖ ≤ δ := by
      have hgG : g x - G x = (c - 1) • G x := by rw [hgdef]; module
      have hcle : c - 1 ≤ 0 := by
        rw [hcdef, sub_nonpos]; exact inv_le_one_of_one_le₀ (by linarith)
      have hc1 : |c - 1| = δ / (1 + δ) := by
        rw [abs_of_nonpos hcle, hcdef]; field_simp; ring
      rw [hgG, norm_smul, Real.norm_eq_abs, hc1, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [hGb x hx, hδpos]
    calc ‖g x - φ x‖ ≤ ‖g x - G x‖ + ‖G x - φ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 2 * δ := by linarith [hGapp x hx]
  obtain ⟨z, hzK, hz⟩ := exists_fixedPoint_of_contDiff hgcd hgmaps
  have h1 : ε ≤ ‖φ z - z‖ := hlow z hzK
  have h2 : ‖g z - φ z‖ < 2 * δ := hgapp z hzK
  rw [hz, norm_sub_rev, hδdef] at h2
  linarith

end Main

end Brouwer

