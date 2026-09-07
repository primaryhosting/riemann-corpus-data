/-
  Brockian/WeylConfining.lean — confining-potential shape lemmas for the RH route.

  ## What is proved

  Hilbert–Pólya needs operators that can realise eigenvalues of arbitrarily large
  modulus (unbounded / confining shape). Bounded multiplication operators cannot:
  any continuous linear map with bound `C` fails on zeros with `‖s − 1/2‖ > C`
  (already in `WeylOperatorChoice`). This file packages the *potential-shape*
  side of that dichotomy:

    * confining predicate (= `V(x) → +∞` as `|x| → ∞`) and Filter form
    * quadratic `V(x) = x²` is a confining candidate
    * continuous potentials with uniform bound `|V| ≤ M` are **not** confining
    * Gate-1 prime-Gaussian (decaying) is therefore not confining
    * confining potentials are unbounded above (not a `CLM` multiplier on `L²`)
    * clear confining-route corollary: any bound-`C` operator misses large zeros

  ## Honest non-claims

  * Does **not** prove RH, nor inhabit `BrockianSystem`.
  * Does **not** prove ESA of `−Δ + V` for confining `V`, nor discrete spectrum.
  * Does **not** compute the essential spectrum of any Schrödinger operator.
  * Multiplication-by-unbounded is recorded as a **shape definition only**.

  Owner: Grok (swarm #2, confining track). Do not claim RH strength.
  Verification (spec §2A): AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylOperatorChoice
import Brockian.SpectralGate1
import Brockian.RiemannScaffold

open MeasureTheory Complex Filter Topology
open Brockian.SpectralGate1 Brockian.RiemannScaffold
open Brockian.Weyl.OperatorChoice

namespace Brockian.Weyl.Confining

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Confining predicate (refines `ConfiningPotentialCandidate`) -/

/-- **Confining growth:** for every height `C` there is a radius past which
`V` stays at least `C`. Equivalent to `Tendsto V (comap abs atTop) atTop`. -/
def IsConfining (V : ℝ → ℝ) : Prop :=
  ∀ C : ℝ, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → C ≤ V x

/-- Packaging as the existing candidate structure. -/
theorem ConfiningPotentialCandidate.isConfining (c : ConfiningPotentialCandidate) :
    IsConfining c.V :=
  c.confining

/-- Build a candidate from continuity + confining growth. -/
noncomputable def ConfiningPotentialCandidate.of_isConfining (V : ℝ → ℝ)
    (hcont : Continuous V) (hconf : IsConfining V) : ConfiningPotentialCandidate where
  V := V
  continuous := hcont
  confining := hconf

/-- **Filter form of confining.** `V(x) → +∞` as `|x| → ∞`. -/
theorem isConfining_iff_tendsto (V : ℝ → ℝ) :
    IsConfining V ↔ Tendsto V (comap abs atTop) atTop := by
  constructor
  · intro h
    refine tendsto_atTop.mpr fun C => ?_
    obtain ⟨R, hR⟩ := h C
    exact mem_comap.2 ⟨Set.Ici R, Ici_mem_atTop R, fun x hx => hR x hx⟩
  · intro h C
    have hev : ∀ᶠ x in comap abs atTop, C ≤ V x := tendsto_atTop.1 h C
    obtain ⟨t, ht, hpre⟩ := mem_comap.1 hev
    obtain ⟨R, hR⟩ := mem_atTop_sets.1 ht
    refine ⟨R, fun x hx => hpre (hR |x| hx)⟩

/-! ### Quadratic example `V(x) = x²` -/

/-- **Quadratic potential is confining.** For every `C` choose
`R = max(0, √C)` (or `0` when `C ≤ 0`): then `|x| ≥ R ⇒ x² ≥ C`. -/
theorem quadratic_isConfining : IsConfining fun x : ℝ => x ^ 2 := by
  intro C
  by_cases hC : C ≤ 0
  · refine ⟨0, fun x _ => le_trans hC (sq_nonneg x)⟩
  · push_neg at hC
    refine ⟨Real.sqrt C, fun x hx => ?_⟩
    have h0 : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
    have : (Real.sqrt C) ^ 2 ≤ |x| ^ 2 :=
      (sq_le_sq₀ h0 (abs_nonneg x)).2 hx
    calc C
        = (Real.sqrt C) ^ 2 := (Real.sq_sqrt (le_of_lt hC)).symm
      _ ≤ |x| ^ 2 := this
      _ = x ^ 2 := sq_abs x

/-- Continuous quadratic as a `ConfiningPotentialCandidate`. -/
noncomputable def quadraticCandidate : ConfiningPotentialCandidate :=
  ConfiningPotentialCandidate.of_isConfining (fun x => x ^ 2)
    (by continuity) quadratic_isConfining

@[simp] theorem quadraticCandidate_V : quadraticCandidate.V = fun x => x ^ 2 := rfl

/-! ### Bounded potentials are not confining -/

/-- **Uniform bound forbids confining growth.** If `|V x| ≤ M` everywhere, then
`IsConfining V` is false: the height `M + 1` can never be reached outside any
radius (in fact nowhere). Continuity is not required. -/
theorem not_isConfining_of_abs_le {V : ℝ → ℝ} {M : ℝ}
    (hbd : ∀ x, |V x| ≤ M) : ¬ IsConfining V := by
  intro hconf
  obtain ⟨R, hR⟩ := hconf (M + 1)
  set x := |R| + 1
  have hx : R ≤ |x| := by
    dsimp [x]
    rw [abs_of_nonneg (by positivity)]
    exact (le_abs_self R).trans (by linarith)
  have hge : M + 1 ≤ V x := hR x hx
  have hle : V x ≤ M := (le_abs_self (V x)).trans (hbd x)
  linarith

/-- A `DecayingPotentialCandidate` (bounded continuous) is never confining. -/
theorem decaying_not_isConfining (c : DecayingPotentialCandidate) :
    ¬ IsConfining c.V :=
  not_isConfining_of_abs_le c.bound

/-- A confining candidate cannot also be a decaying candidate with the same `V`. -/
theorem not_both_decaying_and_confining (d : DecayingPotentialCandidate)
    (c : ConfiningPotentialCandidate) (hV : d.V = c.V) : False := by
  have : IsConfining c.V := c.confining
  rw [← hV] at this
  exact decaying_not_isConfining d this

/-! ### Gate-1 test object vs confining candidate -/

/-- **Documentary packaging.** The prime-Gaussian Gate-1 potential is a decaying
candidate (bound `2`) and therefore **not** confining. It is a legitimate ESA /
bounded-multiplication test object, not a Hilbert–Pólya spectral candidate. -/
theorem primeGaussian_not_isConfining : ¬ IsConfining primeGaussian :=
  not_isConfining_of_abs_le abs_primeGaussian_le_two

/-- Re-export: prime-Gaussian is decaying (from `OperatorChoice`). -/
theorem primeGaussian_is_decaying :
    primeGaussian_decaying.V = primeGaussian ∧
      (∀ x, |primeGaussian_decaying.V x| ≤ primeGaussian_decaying.M) :=
  ⟨rfl, primeGaussian_decaying.bound⟩

/-- Quadratic is confining; prime-Gaussian is not. Shape contrast for RH route. -/
theorem gate1_vs_confining_shape :
    IsConfining quadraticCandidate.V ∧ ¬ IsConfining primeGaussian :=
  ⟨quadraticCandidate.confining, primeGaussian_not_isConfining⟩

/-! ### Confining ⇒ unbounded (cannot be a bounded multiplier) -/

/-- Confining potentials are unbounded above. -/
theorem isConfining_not_bddAbove {V : ℝ → ℝ} (h : IsConfining V) :
    ¬ BddAbove (Set.range V) := by
  intro ⟨M, hM⟩
  have hbd : ∀ x, V x ≤ M := fun x => hM ⟨x, rfl⟩
  -- strengthen to abs bound is not needed: height M+1 already contradicts
  obtain ⟨R, hR⟩ := h (M + 1)
  set x := |R| + 1
  have hx : R ≤ |x| := by
    dsimp [x]
    rw [abs_of_nonneg (by positivity)]
    exact (le_abs_self R).trans (by linarith)
  have : M + 1 ≤ V x := hR x hx
  have : V x ≤ M := hbd x
  linarith

/-- Explicit witnesses: confining `V` exceeds every real height. -/
theorem isConfining_unbounded {V : ℝ → ℝ} (h : IsConfining V) (C : ℝ) :
    ∃ x : ℝ, C < V x := by
  obtain ⟨R, hR⟩ := h (C + 1)
  refine ⟨|R| + 1, ?_⟩
  have hx : R ≤ |(|R| + 1)| := by
    rw [abs_of_nonneg (by positivity)]
    exact (le_abs_self R).trans (by linarith)
  linarith [hR _ hx]

/-- Structure form: confining candidate ⇒ range not bounded above. -/
theorem confiningCandidate_not_bddAbove (c : ConfiningPotentialCandidate) :
    ¬ BddAbove (Set.range c.V) :=
  isConfining_not_bddAbove c.confining

/-! ### Confining-route spectral corollary (re-export / strengthen OperatorChoice) -/

/-- **Any bound-`C` operator misses large zeros.** Re-statement of
`OperatorChoice.not_realize_zero_of_bound_lt` under the confining narrative:
a Hilbert–Pólya candidate that realises a zero with `‖s − 1/2‖ > C` cannot be
a continuous linear map obeying bound `C`. -/
theorem bound_C_blocks_zeros_outside_ball (A : H →L[ℂ] H) {C : ℝ} {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖)
    (hball : C < ‖s - 1 / 2‖)
    (v : H) (hv : v ≠ 0) :
    A v ≠ (-I * (s - 1 / 2)) • v :=
  not_realize_zero_of_bound_lt A hz htriv hs1 hbd hball v hv

/-- Packaged: no eigenvector at the Brockian eigenvalue outside the bound ball. -/
theorem no_brockian_eigenvector_outside_bound (A : H →L[ℂ] H) {C : ℝ} {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖)
    (hball : C < ‖s - 1 / 2‖) :
    ¬ ∃ v : H, v ≠ 0 ∧ A v = (-I * (s - 1 / 2)) • v :=
  rh_operator_needs_unbounded_spectrum A hz htriv hs1 hbd hball

/-- **Prime-Gaussian (Gate-1) instance.** Bound `2`: any nontrivial zero with
`‖s − 1/2‖ > 2` is unrealisable by the prime-Gaussian multiplication operator. -/
theorem primeGaussian_blocks_zeros_outside_two {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hball : (2 : ℝ) < ‖s - 1 / 2‖)
    (v : Lp ℂ 2 (volume : Measure ℝ)) (hv : v ≠ 0) :
    primeGaussianMulCLM v ≠ (-I * (s - 1 / 2)) • v :=
  primeGaussian_not_realize_large_zero hz htriv hs1 hball v hv

/-- **Confining-route moral (machine-checkable half).** If a continuous linear
map realises a nontrivial zero outside every finite ball about `1/2`, then it
admits **no** finite operator bound `C`. (Does not construct such an operator;
only records the necessary unboundedness.) -/
theorem brockian_realizer_admits_no_finite_bound {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (A : H →L[ℂ] H)
    (hrealizes : ∃ v : H, v ≠ 0 ∧ A v = (-I * (s - 1 / 2)) • v) :
    ∀ C : ℝ, ¬ (∀ x, ‖A x‖ ≤ C * ‖x‖) ∨ ¬ (C < ‖s - 1 / 2‖) := by
  intro C
  by_cases hball : C < ‖s - 1 / 2‖
  · left
    intro hbd
    exact no_brockian_eigenvector_outside_bound A hz htriv hs1 hbd hball hrealizes
  · right
    exact hball

/-! ### Unbounded multiplication — shape definition only -/

/-- **Shape note (definition, not a spectral theorem).** A real potential that is
not essentially bounded cannot define a *bounded* multiplication operator on
`L²` via the `mulLpCLM` construction (which requires an `L∞` multiplier).
Confining candidates satisfy this shape (`isConfining_not_bddAbove`).

No claim is made here about the domain of the unbounded multiplication operator,
its spectrum, or essential self-adjointness of `−Δ + V`. -/
def UnboundedMultiplierShape (V : ℝ → ℝ) : Prop :=
  ¬ ∃ M : ℝ, ∀ x, |V x| ≤ M

/-- Confining ⇒ unbounded-multiplier shape. -/
theorem isConfining_unboundedMultiplierShape {V : ℝ → ℝ} (h : IsConfining V) :
    UnboundedMultiplierShape V := by
  intro ⟨M, hM⟩
  exact not_isConfining_of_abs_le hM h

/-- Quadratic has unbounded-multiplier shape. -/
theorem quadratic_unboundedMultiplierShape :
    UnboundedMultiplierShape fun x : ℝ => x ^ 2 :=
  isConfining_unboundedMultiplierShape quadratic_isConfining

/-- Prime-Gaussian does **not** have unbounded-multiplier shape (bound `2`). -/
theorem primeGaussian_not_unboundedMultiplierShape :
    ¬ UnboundedMultiplierShape primeGaussian := by
  intro h
  exact h ⟨2, abs_primeGaussian_le_two⟩

end Brockian.Weyl.Confining
