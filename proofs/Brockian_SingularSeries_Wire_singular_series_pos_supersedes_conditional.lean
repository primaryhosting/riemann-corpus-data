/-
  Brockian/SingularSeriesWire.lean — clean downstream API for unconditional singular-series
  positivity.

  Purpose: let Goldbach / sieve modules stop threading the old conditional hypothesis
  `h_conv` of `Brockian.SingularSeries.singular_series_pos`. The analytic work that
  discharges `h_conv` lives in `Brockian.SingularSeries.Convergence`
  (`singularSeriesFinite_tendsto_pos`, `singular_series_pos'`). This module re-exports
  that result under stable names and records the supersession as a proved implication.

  What is proved (all hole-free, axiom-clean over Mathlib's core):
    * `IsAdmissible`                         : the ν_p < p predicate used by the API
    * `singular_series_pos_unconditional`    : re-export of Convergence.singular_series_pos'
    * `singular_series_pos_of_admissible`    : same, raw hypothesis form (drop-in shape)
    * `singularSeriesFinite_tendsto_pos_of_admissible` : re-export of the tendsto fact
    * `singular_series_finite_pos_of_admissible` : finite-product positivity under IsAdmissible
    * `singular_series_pos_supersedes_conditional` : comparison lemma — the conditional
      `singular_series_pos` is recovered from admissibility alone (h_conv free)

  What this is NOT:
    * Not a Goldbach claim (no representation count, no Hardy–Littlewood main term).
    * Not a rewrite of SingularSeries / Convergence (import-only dependency).

  Verification (spec §2A):
    - `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}
    - AXLE independent : verified @ lean-4.32.0 (see registry/attestations/SingularSeriesWire.json)
-/
import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesConvergence

set_option linter.unusedVariables false
set_option autoImplicit false

open scoped BigOperators
open Filter Topology
open Brockian.SingularSeries
open Brockian.SingularSeries.Convergence

namespace Brockian.SingularSeries.Wire

/-! ## Admissibility packaging -/

/-- Admissibility for a finite integer tuple `G` in the singular-series sense:
`ν_p(G) < p` for every prime `p` (no local obstruction). -/
def IsAdmissible (G : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → nu_p G p < p

/-- Unpack `IsAdmissible` to the raw hypothesis form used by Convergence. -/
theorem isAdmissible_raw {G : Finset ℕ} (h : IsAdmissible G) :
    ∀ p : ℕ, Nat.Prime p → nu_p G p < p :=
  h

/-! ## Unconditional positivity (downstream entry point) -/

/-- **Unconditional singular-series positivity.** Re-export / alias of
`Brockian.SingularSeries.Convergence.singular_series_pos'`: if `G` is admissible then
`0 < singularSeries G`, with no extra `h_conv` hypothesis. -/
theorem singular_series_pos_unconditional (G : Finset ℕ)
    (h_adm : IsAdmissible G) :
    0 < singularSeries G :=
  singular_series_pos' G h_adm

/-- Same statement with the raw prime-by-prime hypothesis (drop-in shape matching
`singular_series_pos'` / older call sites that do not use `IsAdmissible`). -/
theorem singular_series_pos_of_admissible (G : Finset ℕ)
    (h_adm : ∀ p : ℕ, Nat.Prime p → nu_p G p < p) :
    0 < singularSeries G :=
  singular_series_pos' G h_adm

/-! ## Convergence and finite-product helpers -/

/-- Partial Euler products tend to a strictly positive limit under admissibility.
Re-export of `singularSeriesFinite_tendsto_pos` for modules that need the `Tendsto`
fact itself (not only positivity of the limit definition). -/
theorem singularSeriesFinite_tendsto_pos_of_admissible (G : Finset ℕ)
    (h_adm : IsAdmissible G) :
    ∃ S : ℝ, 0 < S ∧ Tendsto (singularSeriesFinite G) atTop (nhds S) :=
  singularSeriesFinite_tendsto_pos G h_adm

/-- Finite singular-series products stay positive under the same admissibility
hypothesis (re-packaging of `singular_series_finite_pos`). -/
theorem singular_series_finite_pos_of_admissible (G : Finset ℕ) (P : ℕ)
    (h_adm : IsAdmissible G) :
    0 < singularSeriesFinite G P :=
  singular_series_finite_pos G P h_adm

/-! ## Supersession of the conditional API -/

/-- **Comparison / supersession lemma.** The conditional theorem
`Brockian.SingularSeries.singular_series_pos` required an explicit convergence
hypothesis `h_conv`. Under admissibility that hypothesis is free
(`singularSeriesFinite_tendsto_pos`), so the conditional statement is recovered
without supplying `h_conv` by hand. Downstream code should prefer
`singular_series_pos_unconditional` / `singular_series_pos_of_admissible`. -/
theorem singular_series_pos_supersedes_conditional (G : Finset ℕ)
    (h_adm : ∀ p : ℕ, Nat.Prime p → nu_p G p < p) :
    0 < singularSeries G :=
  singular_series_pos G (singularSeriesFinite_tendsto_pos G h_adm)

/-- Under admissibility, the `h_conv` package expected by the old conditional theorem
is available on the nose (proved implication, not a documentation-only note). -/
theorem h_conv_of_admissible (G : Finset ℕ)
    (h_adm : IsAdmissible G) :
    ∃ S : ℝ, 0 < S ∧ Tendsto (singularSeriesFinite G) atTop (nhds S) :=
  singularSeriesFinite_tendsto_pos G h_adm

/-- Equivalence of packaging: `IsAdmissible` is definitionally the raw hypothesis. -/
theorem isAdmissible_iff (G : Finset ℕ) :
    IsAdmissible G ↔ ∀ p : ℕ, Nat.Prime p → nu_p G p < p :=
  Iff.rfl

end Brockian.SingularSeries.Wire
