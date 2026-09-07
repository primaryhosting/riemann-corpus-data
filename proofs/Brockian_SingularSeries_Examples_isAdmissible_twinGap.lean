/-
  Brockian/SingularSeriesExamples.lean — concrete admissible configurations with
  strictly positive singular series, via the SingularSeriesWire API.

  Purpose: instantiate `IsAdmissible` and `singular_series_pos_unconditional` on
  explicit small Hardy–Littlewood offset sets. The twin-gap pattern is
  `G = {0, 2}`; more generally `G = {0, n}` for even `n` (no local obstruction
  at `p = 2`, and a two-point set cannot cover an odd prime's residues).

  What is proved (all hole-free, axiom-clean over Mathlib's core):
    * `evenPair` / `twinGap`               : concrete offset sets `{0, n}`, `{0, 2}`
    * `evenPair_card_le_two`               : |G| ≤ 2
    * `isAdmissible_evenPair`              : Even n → IsAdmissible {0, n}
    * `isAdmissible_twinGap`               : IsAdmissible {0, 2}
    * `singular_series_pos_evenPair`       : Even n → 0 < singularSeries {0, n}
    * `singular_series_pos_twinGap`        : 0 < singularSeries {0, 2}
    * small specializations for n = 2, 4, 6

  What this is NOT:
    * Not a twin-prime theorem, density asymptotic, or Hardy–Littlewood conjecture.
    * Not a Goldbach representation claim (no counting of prime pairs summing to N).
    * Not a rewrite of SingularSeries / Convergence / Wire (import-only dependency).

  Verification (spec §2A):
    - `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}
    - AXLE independent : see registry/attestations/SingularSeriesExamples.json
-/
import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesWire

set_option linter.unusedVariables false
set_option autoImplicit false

open Brockian.SingularSeries
open Brockian.SingularSeries.Wire

namespace Brockian.SingularSeries.Examples

/-! ## Concrete offset sets -/

/-- Two-point Hardy–Littlewood offset set `{0, n}` (binary constellation). -/
def evenPair (n : ℕ) : Finset ℕ :=
  {0, n}

/-- Twin-gap constellation: offsets `{0, 2}`. -/
def twinGap : Finset ℕ :=
  evenPair 2

theorem twinGap_eq : twinGap = ({0, 2} : Finset ℕ) := rfl

theorem evenPair_card_le_two (n : ℕ) : (evenPair n).card ≤ 2 := by
  unfold evenPair
  exact Finset.card_le_two

/-! ## Admissibility for even gaps -/

/-- If `n` is even, the two-point set `{0, n}` is admissible in the singular-series
sense: at `p = 2` both points collapse to residue `0` (so `ν₂ = 1 < 2`), and at
any odd prime a set of size ≤ 2 cannot cover all `p` residues. -/
theorem isAdmissible_evenPair {n : ℕ} (hn : Even n) : IsAdmissible (evenPair n) := by
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    have hdiv : 2 ∣ n := by
      rwa [even_iff_two_dvd] at hn
    have hnmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hsubset :
        (evenPair n).image (fun x : ℕ => x % 2) ⊆ ({0} : Finset ℕ) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      simp [evenPair] at ha ⊢
      rcases ha with rfl | rfl
      · simp
      · exact hnmod
    unfold nu_p
    calc
      ((evenPair n).image (fun x : ℕ => x % 2)).card
          ≤ ({0} : Finset ℕ).card := Finset.card_le_card hsubset
      _ < 2 := by simp
  · have hpgt : 2 < p := by
      have hp2le : 2 ≤ p := hp.two_le
      omega
    unfold nu_p
    exact lt_of_le_of_lt
      (le_trans Finset.card_image_le (evenPair_card_le_two n)) hpgt

/-- Twin-gap set `{0, 2}` is admissible (specialization of the even-pair law). -/
theorem isAdmissible_twinGap : IsAdmissible twinGap :=
  isAdmissible_evenPair (by decide : Even 2)

/-! ## Positive singular series -/

/-- Unconditional positivity of the singular series for every even binary gap. -/
theorem singular_series_pos_evenPair {n : ℕ} (hn : Even n) :
    0 < singularSeries (evenPair n) :=
  singular_series_pos_unconditional (evenPair n) (isAdmissible_evenPair hn)

/-- Twin singular series is strictly positive: `0 < 𝔖({0,2})`. -/
theorem singular_series_pos_twinGap : 0 < singularSeries twinGap :=
  singular_series_pos_evenPair (by decide : Even 2)

/-! ## Small concrete cases -/

theorem isAdmissible_evenPair_two : IsAdmissible (evenPair 2) :=
  isAdmissible_evenPair (by decide : Even 2)

theorem isAdmissible_evenPair_four : IsAdmissible (evenPair 4) :=
  isAdmissible_evenPair (by decide : Even 4)

theorem isAdmissible_evenPair_six : IsAdmissible (evenPair 6) :=
  isAdmissible_evenPair (by decide : Even 6)

theorem singular_series_pos_evenPair_two : 0 < singularSeries (evenPair 2) :=
  singular_series_pos_evenPair (by decide : Even 2)

theorem singular_series_pos_evenPair_four : 0 < singularSeries (evenPair 4) :=
  singular_series_pos_evenPair (by decide : Even 4)

theorem singular_series_pos_evenPair_six : 0 < singularSeries (evenPair 6) :=
  singular_series_pos_evenPair (by decide : Even 6)

/-- Finite Euler products for the twin gap are positive for every prime bound. -/
theorem singular_series_finite_pos_twinGap (P : ℕ) :
    0 < singularSeriesFinite twinGap P :=
  singular_series_finite_pos_of_admissible twinGap P isAdmissible_twinGap

end Brockian.SingularSeries.Examples
