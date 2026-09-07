/-
  Brockian/WeylLawTarget.lean — honest CONDITIONAL schema for Riemann–von Mangoldt
  style eigenvalue counting on an RH-shaped operator.

  ┌───────────────────────────────────────────────────────────────────────────┐
  │  RUNG: OPEN (conditional schema). This file does NOT prove a Weyl law,     │
  │  does NOT prove RH, and does NOT inhabit a Hilbert–Pólya operator.         │
  │                                                                            │
  │  Content:                                                                  │
  │    * abstract counting functions `N_op`, `N_model : ℝ → ℝ`                  │
  │    * `WeylLawMatch` — asymptotic equivalence (ratio → 1)                   │
  │    * classical main-term shape `(T/(2π)) log(T/(2π))` (definition only)    │
  │    * packaging: DiscreteSpectrumCandidate + WeylLawMatch ⇒ counting        │
  │      diverges (non-vacuous real-analysis implication; not a spectral law)  │
  │                                                                            │
  │  Gate-0 (existence of an operator whose actual eigenvalue counting         │
  │  matches Riemann–von Mangoldt / zero counting) is NAMED and left OPEN.     │
  │  Never citable as progress on RH or as a proved Weyl law.                  │
  │                                                                            │
  │  conditional_rung: open  (for packaging implications that take             │
  │  DiscreteSpectrumCandidate / WeylLawMatch as hypotheses)                   │
  └───────────────────────────────────────────────────────────────────────────┘

  Patterns: ConfiningSpectralShape (`DiscreteSpectrumCandidate`,
  `EigenvalueCountingMatchesNT` / ratio packaging). Counting obligations are
  Prop defs — never filled with `True`.

  Honest non-claims:
    * No Weyl-law proof for −Δ+V, no compact-resolvent theorem, no discrete
      spectrum of any Schrödinger operator.
    * No identification of eigenvalues with ζ-zeros / N(T).
    * No instance of `WeylLawCandidate` / `MatchesRiemannVonMangoldt` for a
      concrete RH operator.

  Verification (spec §2A): AXLE independent — @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.ConfiningSpectralShape

set_option autoImplicit false

open Filter Topology Real
open Brockian.Weyl.ConfiningShape

namespace Brockian.Weyl.WeylLawTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Abstract counting functions

Operator-side and model-side counting are abstract maps `ℝ → ℝ`. No claim is
made that either equals a concrete spectral counting function or the classical
zero-counting function `N(T)`. -/

/-- **`N_op`** — abstract operator eigenvalue-counting function (placeholder
*type*, not a concrete count). Conventionally `N_op(T)` counts eigenvalues of
modulus / height ≤ `T`. Left abstract so the schema is not tied to a fake
enumeration of zeros. -/
abbrev N_op := ℝ → ℝ

/-- **`N_model`** — abstract model counting function. Classically the
Riemann–von Mangoldt main term (or the true zero-counting function); here only
a second abstract `ℝ → ℝ` so asymptotic comparison is well-typed. -/
abbrev N_model := ℝ → ℝ

/-! ### Weyl-law match (asymptotic equivalence) -/

/-- **`WeylLawMatch N_op N_model`** — asymptotic equivalence of counting
functions: `N_op T / N_model T → 1` as `T → +∞`.

This is the honest name of the counting half of a Hilbert–Pólya-style Weyl-law
obligation. It is a **Prop definition**, not a theorem and not `True`. No
operator is shown to discharge it. -/
def WeylLawMatch (N_op N_model : ℝ → ℝ) : Prop :=
  Tendsto (fun T : ℝ => N_op T / N_model T) atTop (nhds 1)

/-- Difference form: `N_op T − N_model T → 0`. Stronger than ratio form once
`N_model → +∞` (see `WeylLawMatch_of_diff`). Alias-compatible with
`EigenvalueCountingMatchesNT` from `ConfiningSpectralShape`. -/
def WeylLawMatchDiff (N_op N_model : ℝ → ℝ) : Prop :=
  Tendsto (fun T : ℝ => N_op T - N_model T) atTop (nhds 0)

/-- Difference form is definitionally the ConfiningShape counting match. -/
theorem WeylLawMatchDiff_iff_eigenvalueCountingMatchesNT
    (N_op N_model : ℝ → ℝ) :
    WeylLawMatchDiff N_op N_model ↔ EigenvalueCountingMatchesNT N_op N_model :=
  Iff.rfl

/-- Ratio form is definitionally the ConfiningShape asymptotic. -/
theorem WeylLawMatch_iff_eigenvalueCountingAsymptotic
    (N_op N_model : ℝ → ℝ) :
    WeylLawMatch N_op N_model ↔ EigenvalueCountingAsymptotic N_op N_model :=
  Iff.rfl

/-- **Proved packaging (not a Weyl law):** difference match + divergent model
⇒ ratio match. Reuses the ConfiningShape implication; does not instantiate
zeros of ζ or eigenvalues of any operator. -/
theorem WeylLawMatch_of_diff {N_op N_model : ℝ → ℝ}
    (hmodel : Tendsto N_model atTop atTop)
    (h : WeylLawMatchDiff N_op N_model) :
    WeylLawMatch N_op N_model :=
  eigenvalueCountingAsymptotic_of_matches hmodel h

/-! ### Riemann–von Mangoldt main-term shape (definition, not a theorem about ζ) -/

/-- **Classical main term** of the Riemann–von Mangoldt asymptotic:
`(T / (2π)) · log(T / (2π))`.

This is the *shape* a discrete-spectrum RH model is expected to match, not a
proved formula for zeros of ζ in this repository. Defined for all real `T`
(log is Mathlib's extended real logarithm). -/
noncomputable def riemannVonMangoldtMain (T : ℝ) : ℝ :=
  (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi))

/-- **`MatchesRiemannVonMangoldt N_op`** — operator counting asymptotically
matches the classical main term. Prop definition only; OPEN for any
Hilbert–Pólya candidate. -/
def MatchesRiemannVonMangoldt (N_op : ℝ → ℝ) : Prop :=
  WeylLawMatch N_op riemannVonMangoldtMain

/-- The classical main term diverges: `(T/(2π)) log(T/(2π)) → +∞` as `T → +∞`.
Pure real analysis — not a zero-counting theorem. -/
theorem riemannVonMangoldtMain_tendsto_atTop :
    Tendsto riemannVonMangoldtMain atTop atTop := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith
  have hscale : Tendsto (fun T : ℝ => T / (2 * Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const hπ
  have hlog : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
    tendsto_log_atTop.comp hscale
  unfold riemannVonMangoldtMain
  exact hscale.atTop_mul_atTop₀ hlog

/-! ### Counting divergence from a match (non-vacuous analysis) -/

/-- **Proved implication:** if `N_op ∼ N_model` and `N_model → +∞`, then
`N_op → +∞`. Real analysis on abstract counting functions only. -/
theorem N_op_tendsto_atTop_of_WeylLawMatch {N_op N_model : ℝ → ℝ}
    (hmodel : Tendsto N_model atTop atTop)
    (h : WeylLawMatch N_op N_model) :
    Tendsto N_op atTop atTop := by
  -- Eventually ratio > 1/2 and N_model ≥ 1, so (1/2)·N_model ≤ N_op, and
  -- (1/2)·N_model → +∞, hence N_op → +∞ by monotonicity of atTop.
  have hhalf_model : Tendsto (fun T : ℝ => (1 / 2 : ℝ) * N_model T) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hmodel
  have hle : ∀ᶠ T in atTop, (1 / 2 : ℝ) * N_model T ≤ N_op T := by
    have hquot : ∀ᶠ T in atTop, (1 / 2 : ℝ) < N_op T / N_model T :=
      h.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    have hne : ∀ᶠ T in atTop, (1 : ℝ) ≤ N_model T :=
      (tendsto_atTop.1 hmodel) 1
    filter_upwards [hquot, hne] with T hq hm
    have hm0 : (0 : ℝ) < N_model T := lt_of_lt_of_le zero_lt_one hm
    calc (1 / 2 : ℝ) * N_model T
        ≤ (N_op T / N_model T) * N_model T :=
          mul_le_mul_of_nonneg_right (le_of_lt hq) (le_of_lt hm0)
      _ = N_op T := by field_simp [ne_of_gt hm0]
  exact tendsto_atTop_mono' _ hle hhalf_model

/-- Matching the classical main term forces operator counting to diverge. -/
theorem N_op_tendsto_atTop_of_matches_rvm {N_op : ℝ → ℝ}
    (h : MatchesRiemannVonMangoldt N_op) :
    Tendsto N_op atTop atTop :=
  N_op_tendsto_atTop_of_WeylLawMatch riemannVonMangoldtMain_tendsto_atTop h

/-! ### Discrete-spectrum + Weyl-law packaging

An RH-shaped spectral target needs **both**:
  (1) `DiscreteSpectrumCandidate` — dense/symmetric/real/unbounded point spectrum
      (from `ConfiningSpectralShape`);
  (2) `WeylLawMatch` of its counting function against a divergent model
      (Riemann–von Mangoldt style).

Neither half is discharged here. The packaging implications below are non-vacuous
analysis / field projection — **conditional_rung: open** when read as claims
about an RH operator, because inhabiting the structure is Hilbert–Pólya-strength. -/

/-- **`WeylLawCandidate`** — obligation bundle for an RH-shaped operator with
Weyl-law counting. Fields are genuine Props/data; **no instance is constructed**.

Gate-0: exhibiting a term of this type for a concrete operator whose `N_op`
counts actual eigenvalues matching zeros of ζ is OPEN (Hilbert–Pólya + Weyl
law strength). Leave uninhabited. -/
structure WeylLawCandidate (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- Densely-defined candidate operator. -/
  T : H →ₗ.[ℂ] H
  /-- Discrete-spectrum shape obligations (ConfiningSpectralShape). -/
  discrete : DiscreteSpectrumCandidate T
  /-- Operator-side counting function (abstract). -/
  N_op : ℝ → ℝ
  /-- Model-side counting function (abstract; classically RvM main term). -/
  N_model : ℝ → ℝ
  /-- Model counting diverges (necessary for zeros / eigenvalues of arbitrary height). -/
  model_divergent : Tendsto N_model atTop atTop
  /-- Asymptotic match `N_op ∼ N_model`. -/
  weyl_match : WeylLawMatch N_op N_model

/-- **Packaging (proved, non-vacuous):** a `WeylLawCandidate` forces operator
counting to diverge. Uses the match + model-divergence fields only for the
analytic content; the discrete-spectrum field is part of the bundle for the
RH-shaped reading path (extracted separately).

conditional_rung: open — the implication is real, but inhabiting `WeylLawCandidate`
is open-problem-strength. -/
theorem counting_diverges_of_candidate (c : WeylLawCandidate H) :
    Tendsto c.N_op atTop atTop :=
  N_op_tendsto_atTop_of_WeylLawMatch c.model_divergent c.weyl_match

/-- **Packaging:** discrete-spectrum half of a candidate — point spectrum
unbounded in modulus. Field projection from `DiscreteSpectrumCandidate`. -/
theorem point_spectrum_unbounded_of_candidate (c : WeylLawCandidate H) :
    ∀ C : ℝ, ∃ (μ : ℂ) (v : c.T.domain),
      (v : H) ≠ 0 ∧ (c.T v : H) = μ • (v : H) ∧ C < ‖μ‖ :=
  c.discrete.point_spectrum_unbounded

/-- **Conditional packaging implication (non-vacuous analysis).**
If `T` is a discrete-spectrum candidate **and** its counting function matches a
divergent model, then operator counting diverges.

The discrete hypothesis documents the RH-shaped side-condition of the schema; the
analytic work is the match. **Not** a Weyl-law proof for any Schrödinger operator.

conditional_rung: open. -/
theorem counting_diverges_of_discrete_and_WeylLawMatch
    {T : H →ₗ.[ℂ] H}
    (_hdisc : DiscreteSpectrumCandidate T)
    {N_op N_model : ℝ → ℝ}
    (hmodel : Tendsto N_model atTop atTop)
    (hmatch : WeylLawMatch N_op N_model) :
    Tendsto N_op atTop atTop :=
  N_op_tendsto_atTop_of_WeylLawMatch hmodel hmatch

/-- Same packaging with the classical main term as model.
conditional_rung: open. -/
theorem counting_diverges_of_discrete_and_rvm
    {T : H →ₗ.[ℂ] H}
    (_hdisc : DiscreteSpectrumCandidate T)
    {N_op : ℝ → ℝ}
    (hmatch : MatchesRiemannVonMangoldt N_op) :
    Tendsto N_op atTop atTop :=
  counting_diverges_of_discrete_and_WeylLawMatch _hdisc
    riemannVonMangoldtMain_tendsto_atTop hmatch

/-- Bundle a discrete candidate with an RVM match into a `WeylLawCandidate`
(model fixed to the classical main term). -/
noncomputable def WeylLawCandidate.of_rvm {T : H →ₗ.[ℂ] H}
    (hdisc : DiscreteSpectrumCandidate T) (N_op : ℝ → ℝ)
    (hmatch : MatchesRiemannVonMangoldt N_op) : WeylLawCandidate H where
  T := T
  discrete := hdisc
  N_op := N_op
  N_model := riemannVonMangoldtMain
  model_divergent := riemannVonMangoldtMain_tendsto_atTop
  weyl_match := hmatch

/-! ### Gate-0: satisfiability named, left OPEN -/

/-- **`WeylLawCandidateExists H`** — Gate-0 obligation: *there exists* a
`WeylLawCandidate` on `H`. Not proved. A proof would be Hilbert–Pólya +
Weyl-law strength. Recorded as a Prop container so the claim slot is named
without being asserted (`CONJECTURE` register if nullary Prop). -/
def WeylLawCandidateExists (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  Nonempty (WeylLawCandidate H)

/-- **Hardness direction (proved):** existence of a candidate already yields
divergent operator counting. Why Gate-0 is not discharged here: any instance
must supply a genuine `WeylLawMatch` against a divergent model.
conditional_rung: open. -/
theorem counting_diverges_of_exists (h : WeylLawCandidateExists H) :
    ∃ N_op : ℝ → ℝ, Tendsto N_op atTop atTop := by
  obtain ⟨c⟩ := h
  exact ⟨c.N_op, counting_diverges_of_candidate c⟩

/-- Compatibility: ConfiningShape difference match + divergent model ⇒ ratio
match under the Weyl-law name. Documentary bridge. -/
theorem WeylLawMatch_of_eigenvalueCountingMatchesNT {N_op N_model : ℝ → ℝ}
    (hmodel : Tendsto N_model atTop atTop)
    (h : EigenvalueCountingMatchesNT N_op N_model) :
    WeylLawMatch N_op N_model :=
  WeylLawMatch_of_diff hmodel h

end Brockian.Weyl.WeylLawTarget
