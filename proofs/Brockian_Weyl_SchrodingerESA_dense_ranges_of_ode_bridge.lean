/-
  Brockian/WeylSchrodingerESA.lean — end-to-end Gate-1 assembly for the
  Schrödinger operator −d²/dx² + V on L²(ℝ).

  ## What is closed (this module)

  The **analytic bridge** (`Weyl.Bridge.no_nonzero_L2_solution`) says: a non-real
  L² classical solution of −y″ + V y = λ y is zero. The **von Neumann criterion**
  (`Weyl.Cayley.essentiallySelfAdjoint_iff` + `Weyl.Chain`) says: densely-defined
  symmetric T is essentially self-adjoint iff both deficiency spaces are trivial.

  This file **composes** them under the standard identification hypothesis:

      every non-real adjoint eigenvector of T is (represented by) an L² classical
      solution of the Schrödinger ODE for V.

  That identification is classical for the *maximal/minimal* Schrödinger operator
  with continuous V; constructing T and proving the identification in Lean is the
  remaining Mathlib-scale step. We name it honestly as `DeficiencyRepresentsODE`
  and discharge ESA once it is assumed — plus we fully close the **bounded**
  case already available from SpectralGate1 + Gate1Bounded (no ODE needed).

  ## Theorems

    * `deficiencySpace_eq_bot_of_ode_bridge` — ODE identification + Bridge ⇒
        `ker(T* − z) = ⊥` for Im z ≠ 0
    * `essentiallySelfAdjoint_of_ode_bridge` — full ESA from the identification
        at z = ±i (Gate-1 discharge under ODE identification)
    * `primeGaussian_essentiallySelfAdjoint` — **unconditional**: Brockian
        potential multiplication operator is ESA (from Gate1Bounded)
    * `chain_closed_summary` — documentary Prop packaging the status of the chain

  ## Honest remaining work for full −Δ+V

    1. Construct the minimal operator T_min = −d²/dx² + V on L²
    2. Prove T_min is densely defined and symmetric
    3. Prove DeficiencyRepresentsODE T_min V (distributional solutions are classical)
    4. (Optional) continuous bounded-V ⇒ limit-point for the Weyl route

  Items 1–3 are Mathlib infrastructure; item 4 is Aristotle 2204b385.
-/
import Mathlib
import Brockian.WeylOperator
import Brockian.WeylCayley
import Brockian.WeylChain
import Brockian.WeylBridge
import Brockian.WeylGate1Bounded
import Brockian.SpectralGate1

open MeasureTheory Complex
open Brockian.Weyl.Operator Brockian.Weyl.Cayley Brockian.Weyl.Chain
open Brockian.Weyl.Bridge Brockian.Weyl.Gate1Bounded Brockian.SpectralGate1

namespace Brockian.Weyl.SchrodingerESA

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **ODE identification of deficiency vectors.** Every non-real adjoint
eigenvector of `T` is represented a.e. by a classical L² solution of
`−y″ + V y = z y`. This is the standard fact for the maximal Schrödinger
operator with continuous potential; here it is an explicit hypothesis so the
Gate-1 assembly is honest and non-vacuous when the hypothesis is later discharged. -/
def DeficiencyRepresentsODE (T : H2 →ₗ.[ℂ] H2) (V : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → ∀ (g : T.adjoint.domain),
    g ∈ deficiencySpace T z →
      ∃ (y y' y'' : ℝ → ℂ),
        IsL2Solution V z y y' y'' ∧
          ((∀ x, y x = 0) → (g : H2) = 0)

/-! ### Deficiency triviality from the ODE bridge -/

/-- **Bridge ⇒ deficiency space trivial.** Under `DeficiencyRepresentsODE`, the
already-proved `no_nonzero_L2_solution` forces `ker(T* − z) = ⊥` for every
non-real `z`. -/
theorem deficiencySpace_eq_bot_of_ode_bridge
    (T : H2 →ₗ.[ℂ] H2) (V : ℝ → ℝ)
    (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : DeficiencyRepresentsODE T V)
    {z : ℂ} (hz : z.im ≠ 0) :
    deficiencySpace T z = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  obtain ⟨y, y', y'', hySol, hy_vanish⟩ := hode z hz g hg
  have hy0 : ∀ x, y x = 0 :=
    no_nonzero_L2_solution (V := V) hVc M hV z hz y y' y'' hySol
  exact Subtype.ext (hy_vanish hy0)

/-- **Gate-1 discharge under ODE identification.** A densely-defined symmetric
operator on L² whose non-real deficiency vectors are classical Schrödinger
solutions (for continuous real V) is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_of_ode_bridge
    (T : H2 →ₗ.[ℂ] H2) (hd : Dense (T.domain : Set H2))
    (_hsym : IsSymmetric T)
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : DeficiencyRepresentsODE T V) :
    EssentiallySelfAdjoint T := by
  refine ⟨?_, ?_⟩
  · exact deficiencySpace_eq_bot_of_ode_bridge T V hVc M hV hode (by simp : (I : ℂ).im ≠ 0)
  · exact deficiencySpace_eq_bot_of_ode_bridge T V hVc M hV hode
      (by simp [neg_ne_zero] : ((-I : ℂ).im) ≠ 0)

/-- Same conclusion via the Cayley/Chain form (dense ranges), recorded for the
end-to-end narrative: ODE bridge ⇒ deficiency bot ⇒ dense ranges ⇒ ESA. -/
theorem dense_ranges_of_ode_bridge
    (T : H2 →ₗ.[ℂ] H2) (hd : Dense (T.domain : Set H2))
    (hsym : IsSymmetric T)
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : DeficiencyRepresentsODE T V) :
    Dense (rangeAddI T : Set H2) ∧ Dense (rangeSubI T : Set H2) := by
  have hESA := essentiallySelfAdjoint_of_ode_bridge T hd hsym V hVc M hV hode
  exact (essentiallySelfAdjoint_iff hd).mp hESA

theorem essSelfAdjoint_of_ode_bridge_via_chain
    (T : H2 →ₗ.[ℂ] H2) (hd : Dense (T.domain : Set H2))
    (hsym : IsSymmetric T)
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : DeficiencyRepresentsODE T V) :
    EssentiallySelfAdjoint T := by
  have h := dense_ranges_of_ode_bridge T hd hsym V hVc M hV hode
  exact essSelfAdjoint_of_dense_ranges hd h.1 h.2

/-! ### Unconditional: Brockian potential (bounded multiplication) -/

/-- **Unconditional Gate-1 (potential term).** The prime-Gaussian multiplication
operator on L² is essentially self-adjoint — no ODE identification required. -/
theorem primeGaussian_essentiallySelfAdjoint :
    EssentiallySelfAdjoint (primeGaussianMulCLM.toPMap ⊤) :=
  primeGaussianMul_essentiallySelfAdjoint

/-- Any bounded self-adjoint free part plus the Brockian potential is essentially
self-adjoint (Kato + ESA for bounded operators). -/
theorem free_plus_primeGaussian_essentiallySelfAdjoint
    {T : H2 →L[ℂ] H2} (hT : IsSelfAdjoint T) :
    EssentiallySelfAdjoint ((T + primeGaussianMulCLM).toPMap ⊤) :=
  add_primeGaussian_essentiallySelfAdjoint hT

/-! ### Chain status (honest, machine-checkable packaging) -/

/-- Documentary packaging of the Gate-1 chain for continuous real V.
`closed_under_ode_id` is the theorem above; `potential_unconditional` is Gate1Bounded;
`full_unbounded_laplacian` remains open (construction of −Δ + V). -/
structure Gate1ChainStatus where
  /-- ODE bridge proved: non-real L² solutions vanish. -/
  bridge : ∀ (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (lam : ℂ) (hlam : lam.im ≠ 0) (y y' y'' : ℝ → ℂ)
    (hy : IsL2Solution V lam y y' y''), ∀ x, y x = 0
  /-- Abstract ESA under deficiency↔ODE identification. -/
  closed_under_ode_id : ∀ (T : H2 →ₗ.[ℂ] H2),
    Dense (T.domain : Set H2) → IsSymmetric T →
    ∀ (V : ℝ → ℝ), Continuous V → ∀ M, (∀ x, |V x| ≤ M) →
    DeficiencyRepresentsODE T V → EssentiallySelfAdjoint T
  /-- Potential term unconditional ESA. -/
  potential_unconditional :
    EssentiallySelfAdjoint (primeGaussianMulCLM.toPMap ⊤)

/-- The verified pieces of the Gate-1 chain, as a single inhabitant. -/
noncomputable def gate1_chain_status : Gate1ChainStatus where
  bridge := fun V hVc M hV lam hlam y y' y'' hy =>
    no_nonzero_L2_solution V hVc M hV lam hlam y y' y'' hy
  closed_under_ode_id := fun T hd hsym V hVc M hV hode =>
    essentiallySelfAdjoint_of_ode_bridge T hd hsym V hVc M hV hode
  potential_unconditional := primeGaussian_essentiallySelfAdjoint

end Brockian.Weyl.SchrodingerESA
