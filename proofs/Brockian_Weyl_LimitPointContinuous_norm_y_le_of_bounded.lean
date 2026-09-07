/-
  Brockian/WeylLimitPointContinuous.lean — continuous + bounded real V and the
  Weyl limit-point property at +∞ for the 1D Schrödinger equation

      -y'' + V y = λ y      i.e.      y'' = (V - λ) y.

  ## Why continuity is mandatory (Aristotle proj 17ad1895)

  Bare "bounded V ⇒ limit-point" is **false** under strong pointwise `IsSolution`
  (Dirichlet potential: bounded, discontinuous, every classical solution ≡ 0).
  Aristotle refuted that target. Continuity of V is required. This module never
  claims bare-bounded limit-point.

  ## What is proved (hole-free)

    * Definitions aligned with `Brockian.Weyl.LP` and the Aristotle continuous
      target: `IsSolution`, `L2NearInfty`, `IsLimitPointAtInfty`, `StrongL2NearInfty`,
      `HasFundamentalSystem`.
    * Consistency with `LP` (complex-potential packaging of the same ODE).
    * **`const_continuous_isLimitPoint`**: continuous constant real V and non-real λ
      ⇒ limit-point at +∞ (full classical instance via the verified exponential
      witness of `LP.const_potential_isLimitPoint`). Continuity is recorded
      explicitly (`contBounded_const_isLimitPoint`).
    * Wronskian / Abel engine for solutions of a common ODE.
    * Pointwise bound: `|V| ≤ M` ⇒ `‖y''‖ ≤ (M + ‖λ‖) ‖y‖` for classical solutions.
    * Pure-logic reductions:
        - nontrivial non-L² solution ⇒ limit-point (definitional);
        - fundamental system of which not both members are L² ⇒ limit-point.
    * Bridge packaging: continuous + bounded + Im λ ≠ 0 ⇒ no nonzero global L²
      solution with L² derivative (`Bridge.no_nonzero_L2_solution`).
    * Named open obligation `HasFundamentalSystem` for general continuous V
      (discharged for constants by the exponential basis of the free/const ODE).

  ## What is NOT proved

  Full classical LP for arbitrary continuous bounded V still needs (i) global
  existence of a fundamental system for continuous coefficients (linear ODE on ℝ)
  and (ii) the half-line fact that two independent L² solutions cannot coexist
  under a bound on V (y,y''∈L² ⇒ y'∈L² + Wronskian vanishing). Both are standard
  analysis; they are isolated here as the reduction interface rather than faked.

  Verification: AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylLimitPointBounded
import Brockian.WeylBridge

open MeasureTheory Filter Topology Set Complex
open scoped Topology

namespace Brockian.Weyl.LimitPointContinuous

open Brockian.Weyl.LP
open Brockian.Weyl.Bridge

/-! ### Predicates (Aristotle continuous target, consistent with `LP`) -/

/-- `y` solves `−y″ + V y = λ y` on ℝ. Continuity of `V` is required at theorems. -/
structure IsSolution (V : ℝ → ℝ) (lam : ℂ) (y y' y'' : ℝ → ℂ) : Prop where
  deriv1 : ∀ x, HasDerivAt y (y' x) x
  deriv2 : ∀ x, HasDerivAt y' (y'' x) x
  eqn    : ∀ x, y'' x = ((V x : ℂ) - lam) * y x

/-- Square-integrable near `+∞` from some basepoint (Aristotle form). -/
def L2NearInfty (y : ℝ → ℂ) : Prop :=
  ∃ a : ℝ, IntegrableOn (fun x => ‖y x‖ ^ 2) (Set.Ici a)

/-- Strong L² near ∞: solution and first derivative both L² from some basepoint. -/
def StrongL2NearInfty (y y' : ℝ → ℂ) : Prop :=
  ∃ a : ℝ,
    IntegrableOn (fun x => ‖y x‖ ^ 2) (Set.Ici a) ∧
    IntegrableOn (fun x => ‖y' x‖ ^ 2) (Set.Ici a)

/-- Limit-point at `+∞`: a nontrivial classical solution fails to be L² near `+∞`. -/
def IsLimitPointAtInfty (V : ℝ → ℝ) (lam : ℂ) : Prop :=
  ∃ y y' y'' : ℝ → ℂ, IsSolution V lam y y' y'' ∧ (∃ x, y x ≠ 0) ∧ ¬ L2NearInfty y

/-- A fundamental system: two solutions with non-vanishing Wronskian. -/
def HasFundamentalSystem (V : ℝ → ℝ) (lam : ℂ) : Prop :=
  ∃ y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ,
    IsSolution V lam y1 y1' y1'' ∧ IsSolution V lam y2 y2' y2'' ∧
      ∃ x, y1 x * y2' x - y1' x * y2 x ≠ 0

def Vℂ (V : ℝ → ℝ) : ℝ → ℂ := fun x => (V x : ℂ)

theorem isSolution_iff_isSolutionOn (V : ℝ → ℝ) (lam : ℂ) (y y' y'' : ℝ → ℂ) :
    IsSolution V lam y y' y'' ↔ IsSolutionOn (Vℂ V) lam y y' y'' := by
  constructor
  · intro h; exact ⟨h.deriv1, h.deriv2, h.eqn⟩
  · intro h; exact ⟨h.1, h.2.1, h.2.2⟩

theorem continuous_of_isSolution {V : ℝ → ℝ} {lam : ℂ} {y y' y'' : ℝ → ℂ}
    (hy : IsSolution V lam y y' y'') : Continuous y :=
  continuous_iff_continuousAt.mpr fun x => (hy.deriv1 x).continuousAt

theorem continuous_deriv_of_isSolution {V : ℝ → ℝ} {lam : ℂ} {y y' y'' : ℝ → ℂ}
    (hy : IsSolution V lam y y' y'') : Continuous y' :=
  continuous_iff_continuousAt.mpr fun x => (hy.deriv2 x).continuousAt

theorem L2NearInfty_of_strong {y y' : ℝ → ℂ} (h : StrongL2NearInfty y y') :
    L2NearInfty y := by
  obtain ⟨a, ha, _⟩ := h
  exact ⟨a, ha⟩

/-! ### Constant continuous V (full classical instance) -/

theorem isLimitPoint_of_LP_const (c : ℝ) {lam : ℂ} {a : ℝ}
    (h : LP.IsLimitPointAtInfty (fun _ => (c : ℂ)) lam a) :
    IsLimitPointAtInfty (fun _ => c) lam := by
  obtain ⟨y, y', y'', hsol, hnz, hnot⟩ := h
  refine ⟨y, y', y'', ⟨hsol.1, hsol.2.1, hsol.2.2⟩, hnz, ?_⟩
  intro hL2
  obtain ⟨b, hb⟩ := hL2
  have hy_c : Continuous y := continuous_iff_continuousAt.mpr fun x => (hsol.1 x).continuousAt
  have hcomp : IntegrableOn (fun x => ‖y x‖ ^ 2) (Icc a (max a b)) :=
    (hy_c.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have htail : IntegrableOn (fun x => ‖y x‖ ^ 2) (Ici (max a b)) :=
    hb.mono (Ici_subset_Ici.mpr (le_max_right a b)) le_rfl
  have hcover : (Ici a : Set ℝ) ⊆ Icc a (max a b) ∪ Ici (max a b) := by
    intro x hx
    rcases le_total x (max a b) with hle | hge
    · exact Or.inl ⟨hx, hle⟩
    · exact Or.inr hge
  exact hnot ((hcomp.union htail).mono hcover le_rfl)

theorem continuous_const_potential (c : ℝ) : Continuous (fun _ : ℝ => c) :=
  continuous_const

theorem abs_le_const_potential (c : ℝ) : ∀ x : ℝ, |(fun _ : ℝ => c) x| ≤ |c| := by
  intro x; simp

/-- **Constant continuous V ⇒ limit-point at +∞** (non-real λ). -/
theorem const_continuous_isLimitPoint (c : ℝ) {lam : ℂ} (hlam : lam.im ≠ 0) :
    IsLimitPointAtInfty (fun _ => c) lam :=
  isLimitPoint_of_LP_const c (LP.const_potential_isLimitPoint c hlam 0)

/-- Aristotle packaging: continuous + bound + limit-point, for constant V. -/
theorem contBounded_const_isLimitPoint (c : ℝ) {lam : ℂ} (hlam : lam.im ≠ 0) :
    Continuous (fun _ : ℝ => c) ∧ (∀ x, |(fun _ : ℝ => c) x| ≤ |c|) ∧
      IsLimitPointAtInfty (fun _ => c) lam :=
  ⟨continuous_const_potential c, abs_le_const_potential c,
    const_continuous_isLimitPoint c hlam⟩

/-! ### Wronskian / Abel engine -/

def wronskian (y1 y1' y2 y2' : ℝ → ℂ) : ℝ → ℂ :=
  fun x => y1 x * y2' x - y1' x * y2 x

theorem wronskian_hasDerivAt
    {y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ}
    (hy1 : ∀ x, HasDerivAt y1 (y1' x) x) (hy1' : ∀ x, HasDerivAt y1' (y1'' x) x)
    (hy2 : ∀ x, HasDerivAt y2 (y2' x) x) (hy2' : ∀ x, HasDerivAt y2' (y2'' x) x)
    (x : ℝ) :
    HasDerivAt (wronskian y1 y1' y2 y2') (y1 x * y2'' x - y1'' x * y2 x) x := by
  have e :
      HasDerivAt (fun t => y1 t * y2' t - y1' t * y2 t)
        ((y1' x * y2' x + y1 x * y2'' x) - (y1'' x * y2 x + y1' x * y2' x)) x :=
    ((hy1 x).mul (hy2' x)).sub ((hy1' x).mul (hy2 x))
  have hval :
      ((y1' x * y2' x + y1 x * y2'' x) - (y1'' x * y2 x + y1' x * y2' x))
        = (y1 x * y2'' x - y1'' x * y2 x) := by ring
  rwa [hval] at e

theorem wronskian_isConst
    {q y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ}
    (hy1 : ∀ x, HasDerivAt y1 (y1' x) x) (hy1' : ∀ x, HasDerivAt y1' (y1'' x) x)
    (hy2 : ∀ x, HasDerivAt y2 (y2' x) x) (hy2' : ∀ x, HasDerivAt y2' (y2'' x) x)
    (heq1 : ∀ x, y1'' x = q x * y1 x) (heq2 : ∀ x, y2'' x = q x * y2 x)
    (a b : ℝ) :
    wronskian y1 y1' y2 y2' a = wronskian y1 y1' y2 y2' b := by
  have hd : ∀ x, HasDerivAt (wronskian y1 y1' y2 y2') 0 x := by
    intro x
    have h := wronskian_hasDerivAt hy1 hy1' hy2 hy2' x
    have hz : y1 x * y2'' x - y1'' x * y2 x = 0 := by rw [heq1 x, heq2 x]; ring
    rwa [hz] at h
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) a b

theorem wronskian_const_of_solutions
    {V : ℝ → ℝ} {lam : ℂ} {y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ}
    (h1 : IsSolution V lam y1 y1' y1'') (h2 : IsSolution V lam y2 y2' y2'')
    (a b : ℝ) :
    wronskian y1 y1' y2 y2' a = wronskian y1 y1' y2 y2' b :=
  wronskian_isConst (q := fun x => (V x : ℂ) - lam)
    h1.deriv1 h1.deriv2 h2.deriv1 h2.deriv2
    h1.eqn h2.eqn a b

/-! ### Bounded-V pointwise control of y'' -/

/-- Pointwise bound on the second derivative of a classical solution. -/
theorem norm_y''_le_of_bounded
    {V : ℝ → ℝ} {lam : ℂ} {y y' y'' : ℝ → ℂ} {M : ℝ}
    (hV : ∀ x, |V x| ≤ M) (hy : IsSolution V lam y y' y'') (x : ℝ) :
    ‖y'' x‖ ≤ (M + ‖lam‖) * ‖y x‖ := by
  have heq := hy.eqn x
  calc
    ‖y'' x‖ = ‖((V x : ℂ) - lam) * y x‖ := by rw [heq]
    _ = ‖(V x : ℂ) - lam‖ * ‖y x‖ := norm_mul _ _
    _ ≤ (‖(V x : ℂ)‖ + ‖lam‖) * ‖y x‖ := by gcongr; exact norm_sub_le _ _
    _ = (|V x| + ‖lam‖) * ‖y x‖ := by simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (M + ‖lam‖) * ‖y x‖ := by gcongr; exact hV x

theorem normSq_y''_le_of_bounded
    {V : ℝ → ℝ} {lam : ℂ} {y y' y'' : ℝ → ℂ} {M : ℝ}
    (hV : ∀ x, |V x| ≤ M) (hy : IsSolution V lam y y' y'') (x : ℝ) :
    ‖y'' x‖ ^ 2 ≤ (M + ‖lam‖) ^ 2 * ‖y x‖ ^ 2 := by
  have h := norm_y''_le_of_bounded hV hy x
  have hA : 0 ≤ M + ‖lam‖ := by
    nlinarith [abs_nonneg (V 0), hV 0, norm_nonneg lam]
  have hy0 : 0 ≤ ‖y x‖ := norm_nonneg _
  have h2 : ‖y'' x‖ * ‖y'' x‖ ≤ (M + ‖lam‖) * ‖y x‖ * ‖y'' x‖ := by
    nlinarith [norm_nonneg (y'' x)]
  have h3 : (M + ‖lam‖) * ‖y x‖ * ‖y'' x‖ ≤
      (M + ‖lam‖) * ‖y x‖ * ((M + ‖lam‖) * ‖y x‖) := by gcongr
  calc
    ‖y'' x‖ ^ 2 = ‖y'' x‖ * ‖y'' x‖ := by ring
    _ ≤ (M + ‖lam‖) * ‖y x‖ * ((M + ‖lam‖) * ‖y x‖) := le_trans h2 h3
    _ = (M + ‖lam‖) ^ 2 * ‖y x‖ ^ 2 := by ring

/-! ### Pure-logic limit-point reductions -/

/-- A nontrivial solution that fails L² near ∞ witnesses limit-point. -/
theorem isLimitPoint_of_non_L2_solution
    {V : ℝ → ℝ} {lam : ℂ} {y y' y'' : ℝ → ℂ}
    (hy : IsSolution V lam y y' y'') (hnz : ∃ x, y x ≠ 0) (hL2 : ¬ L2NearInfty y) :
    IsLimitPointAtInfty V lam :=
  ⟨y, y', y'', hy, hnz, hL2⟩

/-- If a fundamental system has a member that is not L² near ∞, the equation is
limit-point at +∞. -/
theorem isLimitPoint_of_fundSystem_member_not_L2
    {V : ℝ → ℝ} {lam : ℂ}
    {y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ}
    (h1 : IsSolution V lam y1 y1' y1'')
    (h2 : IsSolution V lam y2 y2' y2'')
    (hW : ∃ x, wronskian y1 y1' y2 y2' x ≠ 0)
    (hnot : ¬ L2NearInfty y1 ∨ ¬ L2NearInfty y2) :
    IsLimitPointAtInfty V lam := by
  -- Nonzero Wronskian ⇒ each basis solution is nontrivial
  obtain ⟨x0, hx0⟩ := hW
  have hnz1 : ∃ x, y1 x ≠ 0 := by
    by_contra h
    push_neg at h
    have : wronskian y1 y1' y2 y2' x0 = 0 := by
      simp only [wronskian, h x0, h, zero_mul, sub_zero]
      -- need y1' x0 = 0 as well from y1 ≡ 0
      have hy1z : y1 = fun _ => 0 := funext h
      have hy1'z : y1' = fun _ => 0 := by
        funext t
        have hd := h1.deriv1 t
        have : HasDerivAt y1 0 t := by
          rw [hy1z]; exact hasDerivAt_const t 0
        exact hd.unique this
      simp [wronskian, hy1z, hy1'z]
    exact hx0 this
  have hnz2 : ∃ x, y2 x ≠ 0 := by
    by_contra h
    push_neg at h
    have hy2z : y2 = fun _ => 0 := funext h
    have hy2'z : y2' = fun _ => 0 := by
      funext t
      have hd := h2.deriv1 t
      have : HasDerivAt y2 0 t := by
        rw [hy2z]; exact hasDerivAt_const t 0
      exact hd.unique this
    have : wronskian y1 y1' y2 y2' x0 = 0 := by
      simp [wronskian, hy2z, hy2'z]
    exact hx0 this
  rcases hnot with h | h
  · exact isLimitPoint_of_non_L2_solution h1 hnz1 h
  · exact isLimitPoint_of_non_L2_solution h2 hnz2 h

/-- Equivalent packaging: FS + “not both L²” ⇒ limit-point. -/
theorem isLimitPoint_of_fundSystem_not_both_L2
    {V : ℝ → ℝ} {lam : ℂ}
    {y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ}
    (h1 : IsSolution V lam y1 y1' y1'')
    (h2 : IsSolution V lam y2 y2' y2'')
    (hW : ∃ x, wronskian y1 y1' y2 y2' x ≠ 0)
    (hnot : ¬ (L2NearInfty y1 ∧ L2NearInfty y2)) :
    IsLimitPointAtInfty V lam := by
  apply isLimitPoint_of_fundSystem_member_not_L2 h1 h2 hW
  tauto

/-! ### Bridge packaging (continuous + bounded ⇒ global deficiency trivial) -/

/-- Continuous + bounded real V and non-real λ: no nonzero global L² solution
with L² derivative. Re-export of the verified Bridge theorem under the continuous
hypothesis required by Aristotle. -/
theorem no_nonzero_global_L2_of_contBounded
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (lam : ℂ) (hlam : lam.im ≠ 0)
    (y y' y'' : ℝ → ℂ) (hy : IsL2Solution V lam y y' y'') :
    ∀ x, y x = 0 :=
  no_nonzero_L2_solution V hVc M hV lam hlam y y' y'' hy

/-! ### Open interface for the general continuous case -/

/-- Classical analytic step still open as a Mathlib-infrastructure obligation:
under continuous bounded V and non-real λ, any fundamental system has a member
that fails to be L² near ∞. (Equivalent to the bounded-V half-line LP dichotomy
once a fundamental system is known to exist.) -/
def FundSystemLimitPointObligation (V : ℝ → ℝ) (lam : ℂ) : Prop :=
  ∀ y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ,
    IsSolution V lam y1 y1' y1'' → IsSolution V lam y2 y2' y2'' →
      (∃ x, wronskian y1 y1' y2 y2' x ≠ 0) →
        ¬ (L2NearInfty y1 ∧ L2NearInfty y2)

/-- Discharge of the Aristotle continuous-bounded target under the two classical
analytic inputs (fundamental system + half-line dimension obstruction). -/
theorem contBounded_isLimitPoint_of_FS_obligation
    (V : ℝ → ℝ) (_hVc : Continuous V) (_M : ℝ) (_hV : ∀ x, |V x| ≤ _M)
    (lam : ℂ) (_hlam : lam.im ≠ 0)
    (hFS : HasFundamentalSystem V lam)
    (hOb : FundSystemLimitPointObligation V lam) :
    IsLimitPointAtInfty V lam := by
  obtain ⟨y1, y1', y1'', y2, y2', y2'', h1, h2, hW⟩ := hFS
  have hW' : ∃ x, wronskian y1 y1' y2 y2' x ≠ 0 := by
    simpa [wronskian] using hW
  exact isLimitPoint_of_fundSystem_not_both_L2 h1 h2 hW' (hOb y1 y1' y1'' y2 y2' y2'' h1 h2 hW')

/-- Sanity: free Schrödinger at λ = i is limit-point (continuous constant 0). -/
example : IsLimitPointAtInfty (fun _ => (0 : ℝ)) Complex.I :=
  const_continuous_isLimitPoint 0 (by simp)

end Brockian.Weyl.LimitPointContinuous
