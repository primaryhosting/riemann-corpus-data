/-
  Brockian/WeylDeficiencyRegularity.lean — reduction of the last Gate-1 gap
  (`DeficiencyRepresentsODE` for the concrete minimal Schrödinger operator
  `T = −d²/dx² + V`) to a **single, precisely-stated classical regularity fact**.

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

  The open obligation of `Brockian/WeylSchrodingerMinimal.lean` is

      `DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V`,

  i.e. every non-real adjoint eigenvector `g` of the concrete operator `T` is
  represented a.e. by a classical L² solution of `−y″ + V y = z y`. That statement
  bundles three things: (a) *interpretation* of the abstract `LinearPMap` adjoint
  `T*` for the concrete Schwartz core, (b) *elliptic regularity* (a weak/distributional
  solution has a classical `C²` representative), and (c) *L²-representation* plumbing.

  This module **discharges (a) and (c) with genuine Lean proofs** and isolates (b)
  as one named hypothesis in pure analysis terms:

    * `inner_g_schwartz`, `inner_g_schwartz_D2`, `inner_g_potential`,
      `coeFn_potentialMul` — the L² inner product of an arbitrary `g ∈ L²` against
      a Schwartz class `schwartzToL2 φ` (resp. `schwartzToL2 (D2 φ)`, resp.
      `potentialMulCLM V (schwartzToL2 φ)`) equals the corresponding integral
      `∫ conj(g)·φ` (resp. `∫ conj(g)·φ″`, resp. `∫ conj(g)·(V·φ)`).

    * `WeakSolutionRegularity V` — **the isolated classical fact**, stated with NO
      operator theory, NO `LinearPMap`, NO adjoint: for non-real `z` and `g ∈ L²`
      satisfying the weak Schrödinger eigen-equation tested against every Schwartz
      function, there exist `y y' y''` with `IsL2Solution V z y y' y''` and `g =ᵐ y`.
      This is exactly one-dimensional elliptic regularity for a 2nd-order ODE with
      continuous coefficients (weak ⇒ classical + membership in L²).

    * `deficiencyRepresentsODE_of_weakRegularity` — **the reduction theorem**:
      `WeakSolutionRegularity V → DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V`.
      Proved by: unpacking `T* g = z·g` via `LinearPMap.adjoint_isFormalAdjoint`
      against the Schwartz core into the weak integral identity (the (a) content),
      feeding it to `WeakSolutionRegularity`, and pushing the vanishing clause
      `y ≡ 0 ⇒ g = 0` through `Lp.ext` (the (c) content).

    * `schrodinger_essentiallySelfAdjoint_of_weakRegularity` — Gate-1 for the
      concrete `T` reduced all the way to `WeakSolutionRegularity`: composing the
      reduction with `schrodinger_essentiallySelfAdjoint_of_ode`.

  ## What is NOT proved (the honest remaining rung — a rung-3 CONDITIONAL)

  `WeakSolutionRegularity V` is **not** proved and is **not** vacuous: it is a true
  classical theorem (1D elliptic regularity) whose Lean proof needs distributional /
  Sobolev-space regularity infrastructure that Mathlib v4.32.0 does not provide for
  this operator. It is carried as an explicit named hypothesis — never `sorry`'d,
  never discharged by ex-falso, never by making the hypothesis unsatisfiable.

  ## Precise remaining obstruction (stated formally)

  The one missing Mathlib-scale lemma is:

      For `V : ℝ → ℝ` continuous, `z : ℂ` with `z.im ≠ 0`, and `g ∈ L²(ℝ)` such that
        `∀ φ ∈ 𝓢(ℝ,ℂ),  ∫ conj(g)·(−φ″ + V·φ) = conj(z) · ∫ conj(g)·φ`,
      there exist `y, y', y'' : ℝ → ℂ` with `HasDerivAt y (y' ·) ·`,
      `HasDerivAt y' (y'' ·) ·`, `y'' = (V − z)·y`, `MemLp y 2`, `MemLp y' 2`, and
      `g =ᵐ[volume] y`.

  i.e. an L² weak solution of a second-order ODE with continuous coefficients admits
  a twice-differentiable L² representative. This is what `WeakSolutionRegularity`
  packages (in the equivalent split kinetic/potential form used by the reduction).

  Verification: AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylOperator
import Brockian.WeylBridge
import Brockian.WeylSchrodingerESA
import Brockian.WeylSchrodingerMinimal
import Brockian.SpectralGate1

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal Brockian.SpectralGate1

namespace Brockian.Weyl.DeficiencyODE

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-! ### L² pairings against the Schwartz core, as integrals

These convert the abstract L² inner product `⟪g, ·⟫` of a general `g ∈ L²` against
a Schwartz class into the honest integral `∫ conj(g)·(·)`. This is what lets us turn
"`g` is an adjoint eigenvector of the concrete operator" into "`g` weakly solves the
Schrödinger ODE". -/

/-- `⟪g, schwartzToL2 φ⟫ = ∫ conj(g)·φ` for any `g ∈ L²` and Schwartz `φ`. -/
theorem inner_g_schwartz (g : H2) (φ : SchwartzMap ℝ ℂ) :
    ⟪g, schwartzToL2 φ⟫_ℂ = ∫ x, conj ((g : ℝ → ℂ) x) * (φ : ℝ → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_schwartzToL2 φ] with x hx
  rw [hx, RCLike.inner_apply']

/-- `⟪g, schwartzToL2 (D2 φ)⟫ = ∫ conj(g)·φ″`. -/
theorem inner_g_schwartz_D2 (g : H2) (φ : SchwartzMap ℝ ℂ) :
    ⟪g, schwartzToL2 (D2 φ)⟫_ℂ
      = ∫ x, conj ((g : ℝ → ℂ) x) * deriv (deriv (φ : ℝ → ℂ)) x := by
  rw [inner_g_schwartz]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [D2_apply]

/-- Multiplication by `V` acts pointwise a.e. on the Schwartz class. -/
theorem coeFn_potentialMul (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (φ : SchwartzMap ℝ ℂ) :
    (potentialMulCLM V hVc M hV (schwartzToL2 φ) : ℝ → ℂ)
      =ᵐ[volume] fun x => (V x : ℂ) * (φ : ℝ → ℂ) x := by
  unfold potentialMulCLM
  filter_upwards [coeFn_mulLpCLM _ _ _ _ (schwartzToL2 φ), coeFn_schwartzToL2 φ] with x hmul hsch
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at hmul
  rw [hmul, hsch]

/-- `⟪g, potentialMulCLM V (schwartzToL2 φ)⟫ = ∫ conj(g)·(V·φ)`. -/
theorem inner_g_potential (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (g : H2) (φ : SchwartzMap ℝ ℂ) :
    ⟪g, potentialMulCLM V hVc M hV (schwartzToL2 φ)⟫_ℂ
      = ∫ x, conj ((g : ℝ → ℂ) x) * ((V x : ℂ) * (φ : ℝ → ℂ) x) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_potentialMul V hVc M hV φ] with x hx
  rw [hx, RCLike.inner_apply']

/-! ### The isolated classical regularity fact -/

/-- **The single remaining classical fact: 1D elliptic regularity.**

For continuous real `V`, non-real spectral parameter `z`, and `g ∈ L²(ℝ)`
satisfying the **weak Schrödinger eigen-equation** tested against every Schwartz
function `φ`

    `conj(z) · ∫ conj(g)·φ  =  −∫ conj(g)·φ″ + ∫ conj(g)·(V·φ)`

(the left side is `z̄` times the L² pairing `⟨g, φ⟩`; the right side is the L²
pairing of `g` with the weak action `−φ″ + V·φ` of the operator on the test
function — so the line says `g` distributionally solves `(−d²/dx² + V) g = z g`),
there exists a **classical** L² solution `y` of `−y″ + V y = z y` representing `g`
a.e. This is elliptic/ODE regularity (weak ⇒ `C²`, plus `y, y' ∈ L²`); it is stated
with no operator theory so it is exactly the citable analytic lemma. It is an honest,
satisfiable hypothesis (a true classical theorem), not closed by fiat. -/
def WeakSolutionRegularity (V : ℝ → ℝ) : Prop :=
  ∀ (z : ℂ), z.im ≠ 0 → ∀ (g : H2),
    (∀ φ : SchwartzMap ℝ ℂ,
        conj z * ∫ x, conj ((g : ℝ → ℂ) x) * (φ : ℝ → ℂ) x
          = (-(∫ x, conj ((g : ℝ → ℂ) x) * deriv (deriv (φ : ℝ → ℂ)) x))
            + ∫ x, conj ((g : ℝ → ℂ) x) * ((V x : ℂ) * (φ : ℝ → ℂ) x)) →
      ∃ (y y' y'' : ℝ → ℂ),
        Brockian.Weyl.Bridge.IsL2Solution V z y y' y'' ∧ (g : ℝ → ℂ) =ᵐ[volume] y

/-! ### The reduction: weak regularity ⇒ the concrete Gate-1 obligation -/

/-- **THE REDUCTION.** For the concrete minimal operator `T = −d²/dx² + V`
(bounded continuous real `V`), the elliptic-regularity hypothesis
`WeakSolutionRegularity V` implies the exact Gate-1 obligation
`DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V`.

The proof does the genuine work around the isolated fact: it unpacks the abstract
adjoint eigen-equation `T* g = z·g` against the dense Schwartz core (via
`LinearPMap.adjoint_isFormalAdjoint`, `schrodingerPMap_toFun_ofInjective`,
`coreMap_apply`, and the integral pairings above) into the concrete weak integral
identity, applies `WeakSolutionRegularity`, and discharges the vanishing clause
`y ≡ 0 ⇒ g = 0` through `Lp.ext`. -/
theorem deficiencyRepresentsODE_of_weakRegularity
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hreg : WeakSolutionRegularity V) :
    Brockian.Weyl.SchrodingerESA.DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V := by
  intro z hz g hg
  have heig : (schrodingerPMap V hVc M hV).adjoint g = z • ((g : H2)) :=
    (mem_deficiencySpace_iff (schrodingerPMap V hVc M hV) z g).mp hg
  have hdense := schrodingerPMap_dense V hVc M hV
  -- (a): unpack the abstract adjoint eigen-equation into the concrete weak form
  have hweak : ∀ φ : SchwartzMap ℝ ℂ,
      conj z * ∫ x, conj (((g : H2) : ℝ → ℂ) x) * (φ : ℝ → ℂ) x
        = (-(∫ x, conj (((g : H2) : ℝ → ℂ) x) * deriv (deriv (φ : ℝ → ℂ)) x))
          + ∫ x, conj (((g : H2) : ℝ → ℂ) x) * ((V x : ℂ) * (φ : ℝ → ℂ) x) := by
    intro φ
    have hFA := LinearPMap.adjoint_isFormalAdjoint hdense g
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective φ)
    rw [heig, inner_smul_left, schrodingerPMap_toFun_ofInjective,
      LinearEquiv.ofInjective_apply, coreMap_apply, inner_add_right, inner_neg_right] at hFA
    rw [inner_g_schwartz (g : H2) φ, inner_g_schwartz_D2 (g : H2) φ,
      inner_g_potential V hVc M hV (g : H2) φ] at hFA
    exact hFA
  -- (b): the isolated regularity fact produces a classical L² solution representing g
  obtain ⟨y, y', y'', hsol, hgy⟩ := hreg z hz (g : H2) hweak
  refine ⟨y, y', y'', hsol, ?_⟩
  -- (c): vanishing of the classical solution forces the L² element to vanish
  intro hy0
  have hg0 : ((g : H2) : ℝ → ℂ) =ᵐ[volume] (⇑(0 : H2)) := by
    filter_upwards [hgy, Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal)) (μ := (volume : Measure ℝ))]
      with x hx hz0
    rw [hx, hy0 x, hz0, Pi.zero_apply]
  exact Lp.ext hg0

/-! ### Gate-1 for the concrete operator, reduced to weak regularity -/

/-- **Gate-1 for the concrete minimal operator, reduced to one classical fact.**
`T = −d²/dx² + V` (bounded continuous real `V`) is essentially self-adjoint given
only `WeakSolutionRegularity V` (1D elliptic regularity). Composes the reduction
`deficiencyRepresentsODE_of_weakRegularity` with the conditional Gate-1 assembly
`schrodinger_essentiallySelfAdjoint_of_ode`. Honest: the sole hypothesis is the
named, satisfiable regularity statement — not hidden, not vacuous. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hreg : WeakSolutionRegularity V) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) :=
  schrodinger_essentiallySelfAdjoint_of_ode V hVc M hV
    (deficiencyRepresentsODE_of_weakRegularity V hVc M hV hreg)

/-- Documentary packaging: the concrete Gate-1 state after this reduction — the
elliptic-regularity gap is now a single named analysis hypothesis with no operator
theory in its statement. -/
structure ReducedGate1Status (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) where
  /-- The abstract Gate-1 obligation follows from the isolated regularity fact. -/
  reduction : WeakSolutionRegularity V →
    Brockian.Weyl.SchrodingerESA.DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V
  /-- ESA follows from the isolated regularity fact. -/
  esa : WeakSolutionRegularity V → EssentiallySelfAdjoint (schrodingerPMap V hVc M hV)

/-- The verified inhabitant of the reduced Gate-1 state. -/
def reduced_gate1_status (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    ReducedGate1Status V hVc M hV where
  reduction := deficiencyRepresentsODE_of_weakRegularity V hVc M hV
  esa := schrodinger_essentiallySelfAdjoint_of_weakRegularity V hVc M hV

end Brockian.Weyl.DeficiencyODE
