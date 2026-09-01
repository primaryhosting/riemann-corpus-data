/-
  Aristotle target — GENERAL BOUNDED-V ⇒ LIMIT-POINT at ∞.

  The `Brockian.Weyl.LP` module proved the CONSTANT-potential case
  (`const_potential_isLimitPoint`). This is the genuine general case that was left
  OPEN: for any BOUNDED real potential V and any non-real spectral parameter λ, the
  Schrödinger equation −y″ + V y = λ y is in the limit-point case at ∞ (there is a
  solution that is NOT square-integrable near ∞). This is the ODE analysis link that,
  together with the verified radius dichotomy and the von Neumann criterion, closes
  Gate 1 for a bounded potential.

  Definitions are inlined so the file is self-contained (import Mathlib only).
-/
import Mathlib

open MeasureTheory Filter Topology

namespace Brockian.Weyl.BoundedVTarget

/-- `y` solves `−y″ + V y = λ y`, i.e. `y″ = (V − λ) y`, on all of ℝ (complex-valued,
real variable), with `y'` its derivative and `y''` its second derivative. -/
structure IsSolution (V : ℝ → ℝ) (lam : ℂ) (y y' y'' : ℝ → ℂ) : Prop where
  deriv1 : ∀ x, HasDerivAt y (y' x) x
  deriv2 : ∀ x, HasDerivAt y' (y'' x) x
  eqn    : ∀ x, y'' x = ((V x : ℂ) - lam) * y x

/-- `y` is square-integrable near `+∞` (from some point `a` on). -/
def L2NearInfty (y : ℝ → ℂ) : Prop :=
  ∃ a : ℝ, IntegrableOn (fun x => ‖y x‖ ^ 2) (Set.Ici a)

/-- The equation is in the **limit-point case** at `+∞`: some nontrivial solution fails
to be square-integrable near `+∞` (equivalently, the L²-near-∞ solution space is at
most one-dimensional). -/
def IsLimitPointAtInfty (V : ℝ → ℝ) (lam : ℂ) : Prop :=
  ∃ y y' y'' : ℝ → ℂ, IsSolution V lam y y' y'' ∧ (∃ x, y x ≠ 0) ∧ ¬ L2NearInfty y

/-- The bounded Dirichlet potential, equal to zero at rational points and one at
irrational points. -/
noncomputable def dirichletPotential (x : ℝ) : ℝ :=
  @ite ℝ (x ∈ Set.range ((↑) : ℚ → ℝ)) (Classical.propDecidable _) 0 1

/-- For the Dirichlet potential, every classical solution (in the strong sense used
by `IsSolution`) is identically zero. -/
lemma dirichletPotential_solution_zero (lam : ℂ) (y y' y'' : ℝ → ℂ)
    (hy : IsSolution dirichletPotential lam y y' y'') :
    ∀ x, y x = 0 := by
  intro x
  by_contra hne
  -- y is continuous (since it has a derivative)
  have hy_cont : Continuous y := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hy.deriv1 x).continuousAt
  -- Since y x ≠ 0 and y is continuous, there's a ball around x where y is nonzero
  obtain ⟨ε, hεpos, hball⟩ : ∃ ε > (0 : ℝ), ∀ z, |z - x| < ε → y z ≠ 0 := by
    have := Metric.continuous_iff.mp hy_cont x (‖y x‖) (norm_pos_iff.mpr hne)
    obtain ⟨δ, hδpos, hδ⟩ := this
    use δ, hδpos
    intro z hz hc
    specialize hδ z hz
    simp [hc] at hδ
  -- Pick a rational point q in (x - ε/2, x + ε/2)
  obtain ⟨q, hq_in⟩ : ∃ q : ℚ, x - ε/2 < q ∧ q < x + ε/2 := exists_rat_btwn (by linarith : x - ε/2 < x + ε/2)
  -- Pick an irrational point r in (x - ε/2, x + ε/2)
  obtain ⟨r, hr_in, hr_irr⟩ : ∃ r : ℝ, x - ε/2 < r ∧ r < x + ε/2 ∧ r ∉ Set.range (Rat.cast : ℚ → ℝ) := by
    have := exists_irrational_btwn (by linarith : x - ε/2 < x + ε/2)
    tauto
  -- Both q and r are in the ε-ball, so y(q) ≠ 0 and y(r) ≠ 0
  have hq_ball : |q - x| < ε := by
    rw [abs_lt]
    constructor <;> linarith
  have hr_ball : |r - x| < ε := by
    rw [abs_lt]
    constructor <;> linarith
  have hyq : y q ≠ 0 := hball q hq_ball
  have hyr : y r ≠ 0 := hball r hr_ball
  -- y'' at q and r
  have hyq'' : y'' q = (dirichletPotential q - lam) * y q := hy.eqn q
  have hyr'' : y'' r = (dirichletPotential r - lam) * y r := hy.eqn r
  -- dirichletPotential q = 0 (q is rational)
  have hpot_q : dirichletPotential q = 0 := by
    unfold dirichletPotential
    have h : (q : ℝ) ∈ Set.range (Rat.cast : ℚ → ℝ) := ⟨q, rfl⟩
    simp [h]
  -- dirichletPotential r = 1 (r is irrational)
  have hpot_r : dirichletPotential r = 1 := by
    unfold dirichletPotential
    have h : r ∉ Set.range (Rat.cast : ℚ → ℝ) := hr_irr.2
    simp [h]
  -- Simplify y'' at q and r
  rw [hpot_q] at hyq''
  rw [hpot_r] at hyr''
  -- y'' is the derivative of y', so y' is differentiable
  have hy'_diff : Differentiable ℝ y' := fun x => (hy.deriv2 x).differentiableAt
  -- The constraint: y'' = (1 - lam) * y a.e. (all except rationals, which have measure 0)
  have hy''_ae : ∀ᵐ t ∂MeasureTheory.volume, y'' t = (1 - lam) * y t := by
    have h_count : Set.Countable (Set.range (Rat.cast : ℚ → ℝ)) := Set.countable_range _
    have h_meas : MeasureTheory.volume (Set.range (Rat.cast : ℚ → ℝ)) = 0 := h_count.measure_zero MeasureTheory.volume
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at h_meas
    filter_upwards [h_meas]
    intro t ht_irr
    have hpot_t : dirichletPotential t = 1 := by
      unfold dirichletPotential
      simp [ht_irr]
    exact hy.eqn t ▸ by rw [hpot_t]; module
  -- Use FTC: y'(b) - y'(a) = ∫_a^b y'' = ∫_a^b (1-lam)*y (a.e.)
  -- So the derivative of y' at q is (1-lam)*y(q), not -lam*y(q)
  -- Since y(q) ≠ 0, this is a contradiction
  have h1 : deriv y' q = y'' q := (hy.deriv2 q).deriv
  have h2 : deriv y' q = (1 - lam) * y q := by
    -- Define F(x) = ∫_q^x (1 - lam) * y(t) dt
    let F : ℝ → ℂ := fun x => ∫ t in q..x, (1 - lam) * y t
    -- F is an antiderivative of (1 - lam) * y
    have hF_deriv : ∀ x, HasDerivAt F ((1 - lam) * y x) x := by
      intro x
      have hcont : Continuous fun t => (1 - lam) * y t := by continuity
      have hint : IntervalIntegrable (fun t => (1 - lam) * y t) MeasureTheory.volume q x := hcont.intervalIntegrable q x
      exact intervalIntegral.integral_hasDerivAt_right hint (hcont.stronglyMeasurableAtFilter volume (nhds x)) hcont.continuousAt
    -- Now show y' = F + C for some constant by comparing derivatives
    -- First, we need to show the integral of y'' equals the integral of (1-lam)*y
    have hint_y'' : ∀ a b, ∫ t in a..b, y'' t = ∫ t in a..b, (1 - lam) * y t := by
      intro a b
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hy''_ae] with t ht _
      exact ht
    -- y'' is integrable (same as (1-lam)*y which is continuous)
    have hcont : Continuous fun t => (1 - lam) * y t := by continuity
    have hint_y''_int : ∀ a b, IntervalIntegrable y'' MeasureTheory.volume a b := by
      intro a b
      have h1 : IntervalIntegrable (fun t => (1 - lam) * y t) MeasureTheory.volume a b := hcont.intervalIntegrable a b
      have h2 : (fun t => (1 - lam) * y t) =ᶠ[MeasureTheory.ae (MeasureTheory.volume.restrict (Set.uIoc a b))] y'' := by
        rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        filter_upwards [hy''_ae] with t ht _
        exact ht.symm
      exact h1.congr_ae h2
    -- By FTC: y'(b) - y'(a) = ∫_a^b y'' = ∫_a^b (1-lam)*y = F(b) - F(a)
    have hFTC : ∀ a b, y' b - y' a = F b - F a := by
      intro a b
      have h1 : ∫ t in a..b, y'' t = y' b - y' a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hy.deriv2 x) (hint_y''_int a b)
      have h2 : ∫ t in a..b, (1 - lam) * y t = F b - F a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF_deriv x) (hcont.intervalIntegrable a b)
      rw [← h1, ← h2, hint_y'' a b]
    -- y' - F is constant, so deriv y' = deriv F = (1-lam)*y
    have hconstant : ∀ x, y' x - F x = y' q - F q := by
      intro x
      have := hFTC q x
      -- from y' x - y' q = F x - F q, derive y' x - F x = y' q - F q
      linear_combination this
    have hFq : F q = 0 := by
      simp [F]
    have hy'_eq : ∀ x, y' x = F x + y' q := by
      intro x
      have := hconstant x
      rw [hFq] at this
      rw [sub_eq_iff_eq_add] at this
      linear_combination this
    have hderiv_y' : ∀ x, deriv y' x = deriv F x := by
      intro x
      have heq : y' = fun t => F t + y' q := funext hy'_eq
      rw [heq]
      exact deriv_add_const (y' q)
    rw [hderiv_y' q, (hF_deriv q).deriv]
  rw [h1, hyq''] at h2
  simp at h2
  -- From -(lam * y q) = (1 - lam) * y q, we get y q = 0
  have : y q = 0 := by
    have h3 : -(lam * y q) = (1 - lam) * y q := h2
    have h4 : 0 = (1 : ℂ) * y q := by linear_combination h3
    simp at h4
    exact h4.symm
  exact hyq this

/-- Thus the claimed target is false for pointwise bounded potentials: boundedness
alone does not ensure existence of a nonzero classical solution when no regularity
or measurability assumption is imposed on the potential. -/
theorem dirichletPotential_not_limitPoint (lam : ℂ) :
    ¬ IsLimitPointAtInfty dirichletPotential lam := by
  intro ⟨y, y', y'', hy_sol, ⟨x, hx_ne⟩, _⟩
  exact hx_ne (dirichletPotential_solution_zero lam y y' y'' hy_sol x)

/-- The hypotheses of the requested theorem are simultaneously satisfied by the
counterexample (with the non-real parameter `i`). -/
theorem boundedV_isLimitPoint_counterexample :
    (∀ x, |dirichletPotential x| ≤ (1 : ℝ)) ∧ Complex.I.im ≠ 0 ∧
      ¬ IsLimitPointAtInfty dirichletPotential Complex.I := by
  refine ⟨?_, by simp [Complex.I_im], dirichletPotential_not_limitPoint Complex.I⟩
  intro x
  simp [dirichletPotential]
  split_ifs <;> norm_num

/-
The requested declaration is retained verbatim below, but commented out because it
is refuted by `boundedV_isLimitPoint_counterexample`.

 theorem boundedV_isLimitPoint (V : ℝ → ℝ) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (lam : ℂ) (hlam : lam.im ≠ 0) :
    IsLimitPointAtInfty V lam
-/

end Brockian.Weyl.BoundedVTarget

