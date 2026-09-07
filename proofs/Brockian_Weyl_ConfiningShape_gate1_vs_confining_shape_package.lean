/-
  Brockian/ConfiningSpectralShape.lean — necessary-condition packaging for a
  Hilbert–Pólya-style confining spectral model.

  ## What is packaged / proved

  Hilbert–Pólya needs an operator that can realise nontrivial ζ-zeros as
  eigenvalues `t = −i(s − 1/2)` of arbitrarily large modulus. Bounded CLMs
  cannot (`WeylOperatorChoice` / `WeylConfining`). This file strengthens the
  *shape packaging* without claiming RH:

    * `DiscreteSpectrumCandidate` — Prop bundle of spectral obligations
      (dense domain, symmetry, real eigenvalues, unbounded point spectrum)
      — fields are genuine Props, never filled with `True`
    * `CompactResolventShape` — Prop bundle of potential-shape obligations
      (continuous + confining + unbounded-multiplier) suggested by the
      classical compact-resolvent picture; does **not** prove compact resolvent
    * quadratic `V(x) = x²` discharges the confining shape (reuse)
    * re-export: bound-`C` CLM cannot realise zeros outside the ball of radius `C`
    * confining-route ↔ bounded-obstruction interplay (strengthened packaging)
    * `EigenvalueCountingMatchesNT` — CONDITIONAL OPEN schema (definition only)
      for discrete eigenvalue counting vs Riemann–von Mangoldt `N(T)`; not a
      theorem and not `True`

  ## Honest non-claims

  * Does **not** prove RH, nor inhabit `BrockianSystem`.
  * Does **not** prove ESA of `−Δ + V`, nor compact resolvent, nor discrete spectrum.
  * Does **not** identify eigenvalues with zeros of ζ or with `N(T)`.
  * `DiscreteSpectrumCandidate` / `CompactResolventShape` are obligation bundles;
    no instance of a full Hilbert–Pólya operator is constructed.

  Owner: Grok (swarm). Do not claim RH strength.
  Verification (spec §2A): AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylConfining
import Brockian.WeylOperatorChoice
import Brockian.RiemannScaffold

open MeasureTheory Complex Filter Topology
open Brockian.RiemannScaffold
open Brockian.Weyl.OperatorChoice
open Brockian.Weyl.Confining

namespace Brockian.Weyl.ConfiningShape

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Discrete-spectrum candidate (Prop bundle of obligations) -/

/-- **Discrete-spectrum candidate** — Prop-valued bundle of spectral obligations
for a Hilbert–Pólya-ready densely-defined operator `T`.

Each field is a genuine obligation (domain density, symmetry, reality of
eigenvalues, unbounded point spectrum in modulus). **None is `True`.**

No claim is made that any concrete Schrödinger operator discharges this bundle,
nor that discharging it yields RH (that still needs the zeros ↔ spectrum
correspondence of a `BrockianSystem`, which is not inhabited here). -/
structure DiscreteSpectrumCandidate (T : H →ₗ.[ℂ] H) : Prop where
  /-- `T` is densely defined. -/
  dense_domain : Dense (T.domain : Set H)
  /-- `T` is symmetric (formal self-adjoint). -/
  symm : T.IsFormalAdjoint T
  /-- Eigenvalues attached to nonzero eigenvectors are real. -/
  spectrum_real :
    ∀ (μ : ℂ) (v : T.domain),
      (v : H) ≠ 0 → (T v : H) = μ • (v : H) → μ.im = 0
  /-- Point spectrum unbounded in modulus: for every height `C` there is an
  eigenvalue with `‖μ‖ > C`. Necessary if large zeros are to be realised. -/
  point_spectrum_unbounded :
    ∀ C : ℝ, ∃ (μ : ℂ) (v : T.domain),
      (v : H) ≠ 0 ∧ (T v : H) = μ • (v : H) ∧ C < ‖μ‖

/-- Symmetry alone discharges the reality field (reuse of the scaffold lemma).
Useful packaging: the `spectrum_real` obligation is not free-floating theater. -/
theorem spectrum_real_of_symm {T : H →ₗ.[ℂ] H} (hsymm : T.IsFormalAdjoint T)
    (μ : ℂ) (v : T.domain) (hv : (v : H) ≠ 0)
    (heig : (T v : H) = μ • (v : H)) : μ.im = 0 :=
  symmetric_eigenvalue_im_zero hsymm hv heig

/-- If a discrete-spectrum candidate realises a Brockian eigenvalue
`−I · (s − 1/2)`, that eigenvalue is real — hence `s` is on the critical line
*provided* such a realisation exists. Pure packaging of reality; does not assert
existence of the eigenvector or of `s`. -/
theorem brockian_eigenvalue_real_of_candidate {T : H →ₗ.[ℂ] H}
    (h : DiscreteSpectrumCandidate T) {s : ℂ} {v : T.domain}
    (hv : (v : H) ≠ 0)
    (heig : (T v : H) = (-I * (s - 1 / 2)) • (v : H)) :
    (-I * (s - 1 / 2)).im = 0 :=
  h.spectrum_real _ v hv heig

/-- **Bounded CLMs cannot be discrete-spectrum candidates with unbounded point
spectrum.** If `A` is continuous linear and obeys bound `C`, then no eigenvalue
can have modulus `> C`, so `point_spectrum_unbounded` fails for the full-domain
`LinearPMap` view. -/
theorem not_point_spectrum_unbounded_of_bound (A : H →L[ℂ] H) {C : ℝ}
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖) :
    ¬ ∀ K : ℝ, ∃ (μ : ℂ) (v : (A.toPMap ⊤).domain),
        (v : H) ≠ 0 ∧ (A.toPMap ⊤) v = μ • (v : H) ∧ K < ‖μ‖ := by
  intro h
  obtain ⟨μ, v, hv, heig, hμ⟩ := h (C + 1)
  have heig' : A (v : H) = μ • (v : H) := by
    simpa [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe] using heig
  have hle : ‖μ‖ ≤ C := norm_eigenvalue_le_of_bound A hbd hv heig'
  linarith

/-- Packaging: a bound-`C` continuous linear map does not admit a
`DiscreteSpectrumCandidate` structure on `A.toPMap ⊤` (the unbounded-modulus
field is blocked). -/
theorem not_discreteSpectrumCandidate_of_bound (A : H →L[ℂ] H) {C : ℝ}
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖) :
    ¬ DiscreteSpectrumCandidate (A.toPMap ⊤) := by
  intro h
  exact not_point_spectrum_unbounded_of_bound A hbd h.point_spectrum_unbounded

/-! ### Compact-resolvent shape (potential-side Prop bundle) -/

/-- **Compact-resolvent shape** for a real potential — Prop bundle of *necessary*
potential-shape obligations suggested by the classical picture
(`V` continuous, confining, not a bounded multiplier).

**Does not prove** that `−Δ + V` has compact resolvent, discrete spectrum, or ESA.
Those analytic theorems are OPEN in this repository. Filling this bundle is a
shape precondition, not a spectral theorem. -/
structure CompactResolventShape (V : ℝ → ℝ) : Prop where
  continuous : Continuous V
  confining : IsConfining V
  unbounded_multiplier : UnboundedMultiplierShape V

/-- Confining + continuous ⇒ compact-resolvent *shape* (unbounded-multiplier is
automatic from confining). Still not a spectral theorem. -/
theorem compactResolventShape_of_isConfining {V : ℝ → ℝ}
    (hcont : Continuous V) (hconf : IsConfining V) : CompactResolventShape V where
  continuous := hcont
  confining := hconf
  unbounded_multiplier := isConfining_unboundedMultiplierShape hconf

/-- A confining candidate package yields compact-resolvent shape. -/
theorem compactResolventShape_of_candidate (c : ConfiningPotentialCandidate) :
    CompactResolventShape c.V :=
  compactResolventShape_of_isConfining c.continuous c.confining

/-- **Quadratic potential discharges the shape package.** `V(x) = x²` is continuous,
confining, and an unbounded multiplier — the honest shape half for a confining
route. Compact resolvent of `−Δ + x²` is *not* claimed here. -/
theorem quadratic_compactResolventShape :
    CompactResolventShape fun x : ℝ => x ^ 2 :=
  compactResolventShape_of_isConfining (by continuity) quadratic_isConfining

/-- Re-export: quadratic is confining (from `WeylConfining`). -/
theorem quadratic_isConfining_reexport : IsConfining fun x : ℝ => x ^ 2 :=
  quadratic_isConfining

/-- Re-export: quadratic confining candidate. -/
noncomputable def quadraticCandidate_reexport : ConfiningPotentialCandidate :=
  quadraticCandidate

/-- Bounded (decaying) potentials fail the compact-resolvent shape: confining
fails, hence the bundle cannot hold. -/
theorem not_compactResolventShape_of_abs_le {V : ℝ → ℝ} {M : ℝ}
    (hbd : ∀ x, |V x| ≤ M) : ¬ CompactResolventShape V := by
  intro h
  exact not_isConfining_of_abs_le hbd h.confining

/-- Prime-Gaussian (Gate-1 decaying test object) fails compact-resolvent shape. -/
theorem primeGaussian_not_compactResolventShape :
    ¬ CompactResolventShape primeGaussian :=
  not_compactResolventShape_of_abs_le abs_primeGaussian_le_two

/-- Shape contrast: quadratic has the confining shape package; prime-Gaussian does not. -/
theorem gate1_vs_confining_shape_package :
    CompactResolventShape (fun x : ℝ => x ^ 2) ∧ ¬ CompactResolventShape primeGaussian :=
  ⟨quadratic_compactResolventShape, primeGaussian_not_compactResolventShape⟩

/-! ### Bound-`C` obstruction (re-export / strengthen) -/

/-- **Conditional schema (proved implication):** if `A` is a CLM with bound `C`
and `s` is a nontrivial ζ-zero outside the ball of radius `C` about `1/2`, then
`A` cannot realise `s` as a Hilbert–Pólya eigenvalue.

Re-export of `Confining.bound_C_blocks_zeros_outside_ball` /
`OperatorChoice.not_realize_zero_of_bound_lt`. -/
theorem clm_bound_blocks_zeros_outside_ball (A : H →L[ℂ] H) {C : ℝ} {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖)
    (hball : C < ‖s - 1 / 2‖)
    (v : H) (hv : v ≠ 0) :
    A v ≠ (-I * (s - 1 / 2)) • v :=
  bound_C_blocks_zeros_outside_ball A hz htriv hs1 hbd hball v hv

/-- Packaged existential form: no eigenvector outside the bound ball. -/
theorem clm_bound_no_brockian_eigenvector (A : H →L[ℂ] H) {C : ℝ} {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖)
    (hball : C < ‖s - 1 / 2‖) :
    ¬ ∃ v : H, v ≠ 0 ∧ A v = (-I * (s - 1 / 2)) • v :=
  no_brockian_eigenvector_outside_bound A hz htriv hs1 hbd hball

/-- Prime-Gaussian instance (bound `2`). -/
theorem primeGaussian_clm_blocks_large_zeros {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hball : (2 : ℝ) < ‖s - 1 / 2‖)
    (v : Lp ℂ 2 (volume : Measure ℝ)) (hv : v ≠ 0) :
    primeGaussianMulCLM v ≠ (-I * (s - 1 / 2)) • v :=
  primeGaussian_blocks_zeros_outside_two hz htriv hs1 hball v hv

/-- **Interplay (strengthened packaging):** a potential that is *not* confining
cannot supply the compact-resolvent shape package, while any CLM bound blocks
zeros outside its ball. Together: Gate-1 decaying / bounded multiplications are
spectrally the wrong shape for Hilbert–Pólya; a confining candidate is the
honest necessary shape (still not sufficient for RH). -/
theorem confining_needed_for_shape_and_unbounded_spectrum {V : ℝ → ℝ} :
    CompactResolventShape V → IsConfining V ∧ UnboundedMultiplierShape V :=
  fun h => ⟨h.confining, h.unbounded_multiplier⟩

/-- Documentary corollary: if a CLM realises a zero outside every finite ball,
it admits no finite operator bound (re-export). -/
theorem realizer_admits_no_finite_bound {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (A : H →L[ℂ] H)
    (hrealizes : ∃ v : H, v ≠ 0 ∧ A v = (-I * (s - 1 / 2)) • v) :
    ∀ C : ℝ, ¬ (∀ x, ‖A x‖ ≤ C * ‖x‖) ∨ ¬ (C < ‖s - 1 / 2‖) :=
  brockian_realizer_admits_no_finite_bound hz htriv hs1 A hrealizes

/-! ### Eigenvalue counting vs `N(T)` — CONDITIONAL OPEN schema (definition) -/

/-- **OPEN schema (definition, not a theorem, not `True`):** asymptotic matching
of an operator eigenvalue-counting function `N_op` against a model counting
function `N_model` (classically the Riemann–von Mangoldt `N(T)`).

Stated as a Prop on two real functions:
`N_op T − N_model T → 0` as `T → +∞`.

This is **not proved** for any Hilbert–Pólya operator here. It is the honest
name of the counting obligation that a discrete-spectrum model would still need
to discharge to match zero-counting. Leave uninhabited; do not fill with `True`. -/
def EigenvalueCountingMatchesNT (N_op N_model : ℝ → ℝ) : Prop :=
  Tendsto (fun T : ℝ => N_op T - N_model T) atTop (nhds 0)

/-- Ratio-form counting obligation (definitional, still OPEN):
`N_op / N_model → 1` as `T → +∞`. Named so the obligation is visible; no
existence claim and not filled with `True`. -/
def EigenvalueCountingAsymptotic (N_op N_model : ℝ → ℝ) : Prop :=
  Tendsto (fun T : ℝ => N_op T / N_model T) atTop (nhds 1)

/-- **Proved packaging implication (not a counting theorem for ζ).** If the
difference `N_op − N_model → 0` and the model count `N_model → +∞`, then the
ratio `N_op / N_model → 1`. Does not instantiate either function with zeros of
ζ or with eigenvalues of any operator. -/
theorem eigenvalueCountingAsymptotic_of_matches
    {N_op N_model : ℝ → ℝ}
    (hmodel : Tendsto N_model atTop atTop)
    (h : EigenvalueCountingMatchesNT N_op N_model) :
    EigenvalueCountingAsymptotic N_op N_model := by
  -- N_op / N_model = 1 + (N_op − N_model) · (N_model)⁻¹
  have hinv : Tendsto (fun T : ℝ => (N_model T)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hmodel
  have hfrac : Tendsto (fun T : ℝ => (N_op T - N_model T) * (N_model T)⁻¹)
      atTop (nhds (0 * 0)) :=
    h.mul hinv
  simp only [mul_zero] at hfrac
  have hne : ∀ᶠ T in atTop, N_model T ≠ 0 := by
    filter_upwards [(tendsto_atTop.1 hmodel) 1] with T hT
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hT)
  have heq : ∀ᶠ T in atTop,
      (1 : ℝ) + (N_op T - N_model T) * (N_model T)⁻¹ = N_op T / N_model T := by
    filter_upwards [hne] with T hT
    field_simp [hT]
    ring
  have hsum : Tendsto (fun T : ℝ => (1 : ℝ) + (N_op T - N_model T) * (N_model T)⁻¹)
      atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hfrac
  simp only [add_zero] at hsum
  exact hsum.congr' heq

/-- Symmetry of the difference form (documentary). -/
theorem eigenvalueCountingMatchesNT_comm {N_op N_model : ℝ → ℝ}
    (h : EigenvalueCountingMatchesNT N_op N_model) :
    EigenvalueCountingMatchesNT N_model N_op := by
  dsimp [EigenvalueCountingMatchesNT] at h ⊢
  have hneg : Tendsto (fun T : ℝ => -(N_op T - N_model T)) atTop (nhds 0) := by
    simpa using h.neg
  convert hneg using 1
  ext T
  ring

end Brockian.Weyl.ConfiningShape
