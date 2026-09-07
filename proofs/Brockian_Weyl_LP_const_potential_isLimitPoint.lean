/-
  Brockian/WeylLimitPointBounded.lean — the limit-point property at ∞ for the
  Sturm–Liouville / Schrödinger equation

      -y'' + V y = λ y      i.e.      y'' = (V - λ) y,

  formalised over ℝ → ℂ (real space variable `x`, complex-valued solutions — the
  honest setting for a *nonreal* spectral parameter λ), on the half-line `[a, ∞)`.

  ## The limit-point property (honest, non-rigged definition)

  A solution `y` is *L² near ∞* when `x ↦ ‖y x‖²` is (Lebesgue) integrable on
  `[a, ∞)` (`L2NearInfty`). The equation is in the **limit-point case at ∞**
  (`IsLimitPointAtInfty`) when NOT every solution is L² near ∞ — equivalently, the
  space of L²-near-∞ solutions has dimension ≤ 1 (the total solution space of a
  2nd-order linear ODE being 2-dimensional). This is the standard characterisation
  of the deficiency-index-1 / limit-point alternative, and it is *not* trivially
  true: discharging it requires exhibiting a genuine solution that fails to be L².

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

    * `not_integrableOn_exp_mul_Ioi` — the real-analysis engine: for `r > 0`,
      `x ↦ e^{r x}` is NOT integrable on `(a, ∞)`. Proved from scratch (FTC value
      of the interval integral + divergence vs. convergence of the tail integral).
    * `exists_sqrt_pos_re` — every non-real `z : ℂ` has a square root with strictly
      positive real part (ℂ algebraically closed + a real-part sign flip).
    * `const_potential_isLimitPoint` — **the concrete limit-point theorem**: for a
      *constant* real potential `V ≡ c` and any non-real `λ`, the equation
      `-y'' + c y = λ y` is in the limit-point case at ∞. Witness: `y = e^{μ x}`
      with `μ² = c − λ`, `Re μ > 0` — a genuine solution whose modulus grows
      exponentially, hence is not L² near ∞. (Includes `V ≡ 0`.)

  ## The V-independent algebraic engine (holds for ANY potential)

    * `wronskian`, `wronskian_hasDerivAt` — the Wronskian and its (Lagrange)
      derivative.
    * `wronskian_isConst` — **Abel's identity**: the Wronskian of two solutions of
      the *same* equation `y'' = q y` is constant.
    * `indep_of_wronskian_ne_zero` — non-vanishing Wronskian ⇒ linear independence:
      if `W(a) ≠ 0` and `c₁ y₁ + c₂ y₂ ≡ 0`, then `c₁ = c₂ = 0`. Pure
      Wronskian/derivative algebra, independent of the potential.

  ## Honest scope statement — what is NOT proved, and why

  The **general** implication "bounded V ⇒ limit-point at ∞" is OPEN here. It is a
  true theorem, but its proof is the Weyl nested-circles argument (or the
  deficiency-index computation): for a *nonreal* λ at least one solution is L² near
  ∞, and boundedness of V forces the *second*, independent solution to fail L² —
  which is exactly the analytic content Mathlib v4.32.0 does not supply (no
  Sturm–Liouville theory, no Weyl m-function, no nested-circles construction).

  Note in particular that the naive "two independent L²-near-∞ solutions ⇒ their
  Wronskian is 0" is **FALSE** for a general potential: the *limit-circle* case
  (both independent solutions L² near ∞, Wronskian ≠ 0) genuinely occurs. So the
  distinction limit-point vs. limit-circle is not an algebraic consequence of Abel's
  identity; it is real analysis. We therefore prove the honest V-independent
  algebraic engine (Abel + independence), the constant-potential instance in full,
  and mark the general bounded case OPEN rather than assert it.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Brockian.Weyl.LP

open MeasureTheory intervalIntegral Filter Topology Complex

/-! ### The real-analysis engine: growing exponentials are not integrable at ∞ -/

/-- **Non-integrability of the growing exponential.** For `r > 0`, the function
`x ↦ e^{r x}` is not integrable on `(a, ∞)`.  This is the analytic core of the
limit-point property: a solution whose modulus grows like `e^{r x}` cannot be L²
near ∞.  Proved from first principles — the tail integral `∫ₐ^b e^{r x}` both
converges (were the function integrable) and diverges to `+∞`. -/
theorem not_integrableOn_exp_mul_Ioi {r : ℝ} (hr : 0 < r) (a : ℝ) :
    ¬ IntegrableOn (fun x => Real.exp (r * x)) (Set.Ioi a) := by
  intro hint
  have hconv : Tendsto (fun b => ∫ x in a..b, Real.exp (r * x)) atTop
      (𝓝 (∫ x in Set.Ioi a, Real.exp (r * x))) :=
    intervalIntegral_tendsto_integral_Ioi a hint tendsto_id
  have hval : (fun b => ∫ x in a..b, Real.exp (r * x))
      = fun b => r⁻¹ * (Real.exp (r * b) - Real.exp (r * a)) := by
    funext b
    rw [intervalIntegral.integral_comp_mul_left Real.exp (ne_of_gt hr), integral_exp]
    simp [smul_eq_mul]
  rw [hval] at hconv
  have hexp : Tendsto (fun b : ℝ => Real.exp (r * b)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hr tendsto_id)
  have hdiff : Tendsto (fun b : ℝ => Real.exp (r * b) - Real.exp (r * a)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-Real.exp (r * a)) hexp).congr (by intro x; ring)
  have hdiv : Tendsto (fun b => r⁻¹ * (Real.exp (r * b) - Real.exp (r * a))) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) hdiff
  exact not_tendsto_atTop_of_tendsto_nhds hconv hdiv

/-! ### Square roots with prescribed real-part sign -/

/-- Every **non-real** complex number has a square root with strictly positive real
part.  (`ℂ` is algebraically closed, so a square root exists; a purely imaginary
root would square to a *real* number, contradicting non-reality, so the root has
nonzero real part — flip its sign if needed.) -/
theorem exists_sqrt_pos_re {z : ℂ} (hz : z.im ≠ 0) : ∃ μ : ℂ, μ ^ 2 = z ∧ 0 < μ.re := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (n := 2) (by norm_num)
  have hwre : w.re ≠ 0 := by
    intro h0
    apply hz
    rw [← hw, pow_two, Complex.mul_im, h0]
    ring
  rcases lt_or_gt_of_ne hwre with hneg | hpos
  · exact ⟨-w, by rw [neg_sq]; exact hw, by rw [Complex.neg_re]; linarith⟩
  · exact ⟨w, hw, hpos⟩

/-! ### The Sturm–Liouville / Schrödinger equation and the limit-point property -/

/-- `y` (with prescribed first and second derivatives `y'`, `y''`) is a solution of
`-y'' + V y = λ y` on all of `ℝ`, i.e. `y'' = (V − λ) y`. -/
def IsSolutionOn (V : ℝ → ℂ) (lam : ℂ) (y y' y'' : ℝ → ℂ) : Prop :=
  (∀ x, HasDerivAt y (y' x) x) ∧ (∀ x, HasDerivAt y' (y'' x) x) ∧
    (∀ x, y'' x = (V x - lam) * y x)

/-- `y` is **L² near ∞** (from `a`): `x ↦ ‖y x‖²` is integrable on `[a, ∞)`. -/
def L2NearInfty (a : ℝ) (y : ℝ → ℂ) : Prop :=
  IntegrableOn (fun x => ‖y x‖ ^ 2) (Set.Ici a)

/-- **The limit-point case at ∞.**  The equation `-y'' + V y = λ y` is in the
limit-point case at ∞ (from `a`) when there is a *nontrivial* solution that is NOT
L² near ∞ — equivalently, the space of L²-near-∞ solutions is a proper subspace of
the (2-dimensional) solution space, i.e. has dimension ≤ 1.  This is the honest
deficiency-index-1 characterisation; the zero solution is always L², so any
non-L² solution is automatically nontrivial. -/
def IsLimitPointAtInfty (V : ℝ → ℂ) (lam : ℂ) (a : ℝ) : Prop :=
  ∃ y y' y'' : ℝ → ℂ, IsSolutionOn V lam y y' y'' ∧ (∃ x, y x ≠ 0) ∧ ¬ L2NearInfty a y

/-- Derivative of the complex exponential `x ↦ e^{μ x}` along the real line. -/
private theorem hasDerivAt_cexp_mul (μ : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (μ * (t : ℂ))) (Complex.exp (μ * (x : ℂ)) * μ) x := by
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h : HasDerivAt (fun t : ℝ => μ * (t : ℂ)) μ x := by simpa using h0.const_mul μ
  simpa using h.cexp

/-- **Constant-potential limit-point theorem.**  For a constant real potential
`V ≡ c` and any non-real spectral parameter `λ` (`Im λ ≠ 0`), the equation
`-y'' + c y = λ y` is in the limit-point case at ∞.  The witness is the growing
exponential `y = e^{μ x}` with `μ² = c − λ` and `Re μ > 0`: it solves the equation,
never vanishes, and `‖y x‖² = e^{2 (Re μ) x}` is not integrable on `[a, ∞)`.
Specialises (at `c = 0`) to the free Schrödinger equation `-y'' = λ y`. -/
theorem const_potential_isLimitPoint (c : ℝ) {lam : ℂ} (hlam : lam.im ≠ 0) (a : ℝ) :
    IsLimitPointAtInfty (fun _ => (c : ℂ)) lam a := by
  -- `c − λ` is non-real, so it has a square root `μ` with `Re μ > 0`.
  have hznr : ((c : ℂ) - lam).im ≠ 0 := by
    rw [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_ne_zero]; exact hlam
  obtain ⟨μ, hμ2, hμre⟩ := exists_sqrt_pos_re hznr
  -- The exponential solution and its derivatives.
  set y : ℝ → ℂ := fun x => Complex.exp (μ * (x : ℂ)) with hy_def
  set y' : ℝ → ℂ := fun x => Complex.exp (μ * (x : ℂ)) * μ with hy'_def
  set y'' : ℝ → ℂ := fun x => Complex.exp (μ * (x : ℂ)) * μ * μ with hy''_def
  have hy : ∀ x, HasDerivAt y (y' x) x := fun x => hasDerivAt_cexp_mul μ x
  have hy' : ∀ x, HasDerivAt y' (y'' x) x := fun x => (hasDerivAt_cexp_mul μ x).mul_const μ
  have heq : ∀ x, y'' x = ((fun _ => (c : ℂ)) x - lam) * y x := by
    intro x
    show Complex.exp (μ * (x : ℂ)) * μ * μ = ((c : ℂ) - lam) * Complex.exp (μ * (x : ℂ))
    have hstep : Complex.exp (μ * (x : ℂ)) * μ * μ = Complex.exp (μ * (x : ℂ)) * μ ^ 2 := by ring
    rw [hstep, hμ2]; ring
  refine ⟨y, y', y'', ⟨hy, hy', heq⟩, ⟨a, Complex.exp_ne_zero _⟩, ?_⟩
  -- Not L² near ∞: `‖y x‖² = e^{2 (Re μ) x}`, which is non-integrable on `[a, ∞)`.
  intro hL2
  have hint : IntegrableOn (fun x => ‖y x‖ ^ 2) (Set.Ici a) := hL2
  have hfun : (fun x => ‖y x‖ ^ 2) = fun x => Real.exp (2 * μ.re * x) := by
    funext x
    have hnorm : ‖y x‖ = Real.exp (μ.re * x) := by
      show ‖Complex.exp (μ * (x : ℂ))‖ = Real.exp (μ.re * x)
      rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
    rw [hnorm, pow_two, ← Real.exp_add]
    congr 1; ring
  rw [hfun, integrableOn_Ici_iff_integrableOn_Ioi] at hint
  exact not_integrableOn_exp_mul_Ioi (show (0 : ℝ) < 2 * μ.re by linarith) a hint

/-- **Non-vacuity / sanity.**  The free Schrödinger equation `-y'' = λ y` at the
non-real parameter `λ = i` is in the limit-point case at ∞ (from `0`). -/
example : IsLimitPointAtInfty (fun _ => (0 : ℂ)) Complex.I 0 :=
  const_potential_isLimitPoint 0 (by simp) 0

/-! ### The V-independent algebraic engine (Wronskian) -/

/-- **The Wronskian** `W = y₁ y₂' − y₁' y₂`. -/
def wronskian (y1 y1' y2 y2' : ℝ → ℂ) : ℝ → ℂ :=
  fun x => y1 x * y2' x - y1' x * y2 x

/-- **Infinitesimal Lagrange identity.** `W' = y₁ y₂'' − y₁'' y₂` (pure product
rule; no differential equation assumed). -/
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

/-- **Abel's identity (Wronskian constancy).**  If `y₁` and `y₂` both solve the
*same* equation `y'' = q y`, their Wronskian is constant.  Holds for ANY
coefficient `q` (hence any potential). -/
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
    rw [hz] at h; exact h
  have hdiff : Differentiable ℝ (wronskian y1 y1' y2 y2') := fun x => (hd x).differentiableAt
  have hzero : ∀ x, deriv (wronskian y1 y1' y2 y2') x = 0 := fun x => (hd x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero a b

/-- **Non-vanishing Wronskian ⇒ linear independence.**  If the Wronskian of `y₁, y₂`
is nonzero at some point `a`, then `y₁, y₂` are linearly independent as functions:
`c₁ y₁ + c₂ y₂ ≡ 0` forces `c₁ = c₂ = 0`.  Pure Wronskian/derivative algebra —
independent of any differential equation or potential. -/
theorem indep_of_wronskian_ne_zero
    {y1 y1' y2 y2' : ℝ → ℂ}
    (hy1 : ∀ x, HasDerivAt y1 (y1' x) x) (hy2 : ∀ x, HasDerivAt y2 (y2' x) x)
    {a : ℝ} (hW : wronskian y1 y1' y2 y2' a ≠ 0)
    (c1 c2 : ℂ) (hdep : ∀ x, c1 * y1 x + c2 * y2 x = 0) :
    c1 = 0 ∧ c2 = 0 := by
  -- Differentiating the (identically zero) dependence relation.
  have hder : ∀ x, c1 * y1' x + c2 * y2' x = 0 := by
    intro x
    have hg : HasDerivAt (fun t => c1 * y1 t + c2 * y2 t) (c1 * y1' x + c2 * y2' x) x :=
      ((hy1 x).const_mul c1).add ((hy2 x).const_mul c2)
    have hg0 : HasDerivAt (fun t => c1 * y1 t + c2 * y2 t) 0 x := by
      have hzero : (fun t => c1 * y1 t + c2 * y2 t) = fun _ => (0 : ℂ) := funext hdep
      rw [hzero]; exact hasDerivAt_const x 0
    exact hg.unique hg0
  have e1 := hdep a
  have e2 := hder a
  refine ⟨?_, ?_⟩
  · have hc1 : c1 * wronskian y1 y1' y2 y2' a = 0 := by
      simp only [wronskian]; linear_combination y2' a * e1 - y2 a * e2
    exact (mul_eq_zero.mp hc1).resolve_right hW
  · have hc2 : c2 * wronskian y1 y1' y2 y2' a = 0 := by
      simp only [wronskian]; linear_combination y1 a * e2 - y1' a * e1
    exact (mul_eq_zero.mp hc2).resolve_right hW

end Brockian.Weyl.LP
