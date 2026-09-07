/-
  Brockian/WeylLimitPoint.lean — the Wronskian / Green's-identity core of
  Weyl's limit-point / limit-circle theory for the Sturm–Liouville equation

      -y'' + V y = λ y      i.e.      y'' = q y,   q = V - λ,

  on a half-line, formalised over ℝ → ℂ (a real space variable, complex-valued
  solutions — the honest setting for a *nonreal* spectral parameter λ).

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

  This is the genuinely-formalisable *functional-analytic base* of Weyl theory —
  the algebra and calculus that every treatment of the limit-point / limit-circle
  dichotomy is built on. Nothing here is a definitional restatement; each theorem
  is a real calculus/analysis fact.

    * `wronskian`               — the Wronskian `W = y₁ y₂' − y₁' y₂`.
    * `wronskian_hasDerivAt`    — the infinitesimal Lagrange identity:
                                  `W' = y₁ y₂'' − y₁'' y₂` (no ODE assumed).
    * `wronskian_isConst`       — **Abel / Wronskian constancy**: for two
                                  solutions of the *same* equation `y'' = q y`,
                                  the Wronskian is constant. (The key lemma
                                  underneath the whole dichotomy.)
    * `wronskian_const_one_witness` — a genuine fundamental system (`q = 0`,
                                  `y₁ = 1`, `y₂ = x`) with `W ≡ 1`, discharging
                                  Gate-0 (the hypotheses of `wronskian_isConst`
                                  are satisfiable, non-vacuously).
    * `sturmL`                  — the Sturm–Liouville operator `L y = −y'' + V y`.
    * `lagrange_identity`       — `y₁·(L y₂) − (L y₁)·y₂ = −(y₁ y₂'' − y₁'' y₂)`
                                  (the potential `V` cancels — Green's formula,
                                  pointwise).
    * `green_identity_integral` — the *integrated* Green / Lagrange identity
                                  `∫ₐᵇ (y₁·L y₂ − L y₁·y₂) = W a − W b`.
                                  This is exactly the boundary-Wronskian
                                  computation that makes the minimal operator
                                  symmetric — the entry point to (essential)
                                  self-adjointness.

  ## What is NOT proved, and why (honest scope statement)

  The *full* limit-point criterion (all/one solution L² near ∞ ⇒ essential
  self-adjointness of the minimal operator) is **not reached**. Mathlib v4.32.0
  has no Sturm–Liouville theory, no deficiency-index / von Neumann machinery,
  no `LinearPMap.IsSymmetric` (only `LinearMap.IsSymmetric` for bounded maps and
  a bare `LinearPMap.adjoint`), and no theorem presenting the solution set of a
  2nd-order linear ODE as a 2-dimensional space. Building the dichotomy itself
  requires the analytic Weyl nested-circles argument. This file ships the
  verified base rung and names nothing more than it proves.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Brockian.Weyl

open scoped BigOperators

/-! ### The Wronskian and its derivative -/

/-- **The Wronskian** of two functions `y₁, y₂ : ℝ → ℂ` with prescribed
derivatives `y₁', y₂'`:  `W(x) = y₁(x) y₂'(x) − y₁'(x) y₂(x)`. -/
def wronskian (y1 y1' y2 y2' : ℝ → ℂ) : ℝ → ℂ :=
  fun x => y1 x * y2' x - y1' x * y2 x

/-- **Infinitesimal Lagrange identity.** If `y₁' , y₂'` are the derivatives of
`y₁ , y₂` and `y₁'' , y₂''` the derivatives of `y₁' , y₂'`, then the Wronskian is
differentiable with `W'(x) = y₁(x) y₂''(x) − y₁''(x) y₂(x)`.  No differential
equation is assumed here — this is pure product-rule calculus. -/
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
  rw [hval] at e
  exact e

/-! ### Abel / Wronskian constancy -/

/-- **Wronskian constancy (Abel's identity).** If `y₁` and `y₂` both solve the
*same* second-order equation `y'' = q y` (same coefficient `q`), then their
Wronskian is constant.  This is the linear-algebraic heart of the limit-point /
limit-circle dichotomy: the value of the (nonzero) Wronskian of a fundamental
system is a spectral invariant along the half-line. -/
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
    have hz : y1 x * y2'' x - y1'' x * y2 x = 0 := by
      rw [heq1 x, heq2 x]; ring
    rw [hz] at h; exact h
  have hdiff : Differentiable ℝ (wronskian y1 y1' y2 y2') :=
    fun x => (hd x).differentiableAt
  have hzero : ∀ x, deriv (wronskian y1 y1' y2 y2') x = 0 :=
    fun x => (hd x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero a b

/-- **Gate-0 witness (non-vacuity).** The hypotheses of `wronskian_isConst` are
satisfiable by a genuine, non-degenerate fundamental system: for `q = 0`
(the free equation `y'' = 0`), the solutions `y₁ = 1` and `y₂ = x` are linearly
independent and their Wronskian is the constant `1`.  In particular the "same
equation" hypothesis is not vacuous. -/
theorem wronskian_const_one_witness :
    wronskian (fun _ => (1 : ℂ)) (fun _ => 0) (fun x => (x : ℂ)) (fun _ => 1)
      = fun _ => (1 : ℂ) := by
  funext x
  simp [wronskian]

/-- Sanity: the witness really satisfies the `wronskian_isConst` hypotheses,
so its Wronskian is provably constant via the general theorem (and equals `1`). -/
example (a b : ℝ) :
    wronskian (fun _ => (1 : ℂ)) (fun _ => 0) (fun x => (x : ℂ)) (fun _ => 1) a
      = wronskian (fun _ => (1 : ℂ)) (fun _ => 0) (fun x => (x : ℂ)) (fun _ => 1) b := by
  refine wronskian_isConst
    (q := fun _ => 0)
    (y1'' := fun _ => 0) (y2'' := fun _ => 0)
    (fun x => hasDerivAt_const x 1) (fun x => hasDerivAt_const x 0)
    (fun x => by simpa using (hasDerivAt_id x).ofReal_comp)
    (fun x => hasDerivAt_const x 1)
    (fun x => by ring) (fun x => by ring) a b

/-! ### Green's / Lagrange identity for the Sturm–Liouville operator -/

/-- **The Sturm–Liouville operator** `L y = −y'' + V y`, given the potential `V`
and the (prescribed) second derivative `y''` of `y`. -/
def sturmL (V y y'' : ℝ → ℂ) : ℝ → ℂ :=
  fun x => - y'' x + V x * y x

/-- **Green's (Lagrange) identity, pointwise.**  For any two functions with
prescribed second derivatives and *any* potential `V`,
`y₁·(L y₂) − (L y₁)·y₂ = −(y₁ y₂'' − y₁'' y₂)`.  The potential cancels — this is
the algebraic reason the operator only sees the boundary Wronskian. -/
theorem lagrange_identity (V y1 y1'' y2 y2'' : ℝ → ℂ) (x : ℝ) :
    y1 x * (sturmL V y2 y2'') x - (sturmL V y1 y1'') x * y2 x
      = -(y1 x * y2'' x - y1'' x * y2 x) := by
  simp only [sturmL]; ring

/-- **Integrated Green / Lagrange identity.**  With continuous second
derivatives, the "quadratic form defect" of the Sturm–Liouville operator over an
interval `[a,b]` is exactly the drop in the Wronskian across the endpoints:
`∫ₐᵇ (y₁·L y₂ − L y₁·y₂) = W a − W b`.
This is precisely the boundary computation `⟨y₁, L y₂⟩ − ⟨L y₁, y₂⟩ = [W]ₐᵇ` that
renders the minimal operator symmetric (self-adjointness entry point). -/
theorem green_identity_integral
    {V y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ}
    (hy1 : ∀ x, HasDerivAt y1 (y1' x) x) (hy1' : ∀ x, HasDerivAt y1' (y1'' x) x)
    (hy2 : ∀ x, HasDerivAt y2 (y2' x) x) (hy2' : ∀ x, HasDerivAt y2' (y2'' x) x)
    (hy1''c : Continuous y1'') (hy2''c : Continuous y2'') (a b : ℝ) :
    (∫ x in a..b, y1 x * (sturmL V y2 y2'') x - (sturmL V y1 y1'') x * y2 x)
      = wronskian y1 y1' y2 y2' a - wronskian y1 y1' y2 y2' b := by
  -- continuity of the base functions from their derivatives
  have hy1c : Continuous y1 := continuous_iff_continuousAt.mpr fun x => (hy1 x).continuousAt
  have hy2c : Continuous y2 := continuous_iff_continuousAt.mpr fun x => (hy2 x).continuousAt
  -- the Wronskian's derivative g = y₁ y₂'' − y₁'' y₂ is continuous, hence integrable
  set g : ℝ → ℂ := fun x => y1 x * y2'' x - y1'' x * y2 x with hg
  have hgc : Continuous g := (hy1c.mul hy2''c).sub (hy1''c.mul hy2c)
  have hgint : IntervalIntegrable g MeasureTheory.volume a b :=
    hgc.intervalIntegrable a b
  -- FTC: ∫ g = W b − W a
  have hFTC : (∫ x in a..b, g x) = wronskian y1 y1' y2 y2' b - wronskian y1 y1' y2 y2' a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => wronskian_hasDerivAt hy1 hy1' hy2 hy2' x) hgint
  -- rewrite the integrand via the pointwise Lagrange identity, then integrate −g
  have hrw : (∫ x in a..b, y1 x * (sturmL V y2 y2'') x - (sturmL V y1 y1'') x * y2 x)
      = ∫ x in a..b, -(g x) := by
    apply intervalIntegral.integral_congr
    intro x _
    simpa [hg] using lagrange_identity V y1 y1'' y2 y2'' x
  rw [hrw, intervalIntegral.integral_neg, hFTC]
  ring

end Brockian.Weyl
