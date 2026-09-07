/-
  Brockian/SingularSeriesGaps492500.lean — even binary gaps n ∈ {492, 494, 496, 498, 500}.

  HONEST SCOPE: finite/local singular-series arithmetic only.
  Does NOT claim twin-prime / HL asymptotics / Goldbach transfer / infinitude.
-/
import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesWire
import Brockian.SingularSeriesExamples
import Brockian.SingularSeriesMoreExamples

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Classical
open Real Finset
open Brockian.SingularSeries
open Brockian.SingularSeries.Wire
open Brockian.SingularSeries.Examples
open Brockian.SingularSeries.MoreExamples

namespace Brockian.SingularSeries.Gaps492500

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredNinetyTwo : (evenPair 492).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (492 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredNinetyFour : (evenPair 494).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (494 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredNinetySix : (evenPair 496).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (496 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredNinetyEight : (evenPair 498).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (498 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundred : (evenPair 500).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (500 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredNinetyTwo : IsAdmissible (evenPair 492) :=
  isAdmissible_evenPair (by decide : Even 492)

theorem isAdmissible_evenPair_fourHundredNinetyFour : IsAdmissible (evenPair 494) :=
  isAdmissible_evenPair (by decide : Even 494)

theorem isAdmissible_evenPair_fourHundredNinetySix : IsAdmissible (evenPair 496) :=
  isAdmissible_evenPair (by decide : Even 496)

theorem isAdmissible_evenPair_fourHundredNinetyEight : IsAdmissible (evenPair 498) :=
  isAdmissible_evenPair (by decide : Even 498)

theorem isAdmissible_evenPair_fiveHundred : IsAdmissible (evenPair 500) :=
  isAdmissible_evenPair (by decide : Even 500)

theorem singular_series_pos_evenPair_fourHundredNinetyTwo : 0 < singularSeries (evenPair 492) :=
  singular_series_pos_evenPair (by decide : Even 492)

theorem singular_series_pos_evenPair_fourHundredNinetyFour : 0 < singularSeries (evenPair 494) :=
  singular_series_pos_evenPair (by decide : Even 494)

theorem singular_series_pos_evenPair_fourHundredNinetySix : 0 < singularSeries (evenPair 496) :=
  singular_series_pos_evenPair (by decide : Even 496)

theorem singular_series_pos_evenPair_fourHundredNinetyEight : 0 < singularSeries (evenPair 498) :=
  singular_series_pos_evenPair (by decide : Even 498)

theorem singular_series_pos_evenPair_fiveHundred : 0 < singularSeries (evenPair 500) :=
  singular_series_pos_evenPair (by decide : Even 500)

theorem singular_series_finite_pos_evenPair_fourHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 492) P :=
  singular_series_finite_pos_evenPair (by decide : Even 492) P

theorem singular_series_finite_pos_evenPair_fourHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 494) P :=
  singular_series_finite_pos_evenPair (by decide : Even 494) P

theorem singular_series_finite_pos_evenPair_fourHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 496) P :=
  singular_series_finite_pos_evenPair (by decide : Even 496) P

theorem singular_series_finite_pos_evenPair_fourHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 498) P :=
  singular_series_finite_pos_evenPair (by decide : Even 498) P

theorem singular_series_finite_pos_evenPair_fiveHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 500) P :=
  singular_series_finite_pos_evenPair (by decide : Even 500) P

theorem nu_p_fourHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 492) p = if p = 2 ∨ p ∣ 492 then 1 else 2 :=
  nu_p_evenPair (by decide : (492 : ℕ) ≠ 0) (by decide : Even 492) hp

theorem nu_p_fourHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 494) p = if p = 2 ∨ p ∣ 494 then 1 else 2 :=
  nu_p_evenPair (by decide : (494 : ℕ) ≠ 0) (by decide : Even 494) hp

theorem nu_p_fourHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 496) p = if p = 2 ∨ p ∣ 496 then 1 else 2 :=
  nu_p_evenPair (by decide : (496 : ℕ) ≠ 0) (by decide : Even 496) hp

theorem nu_p_fourHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 498) p = if p = 2 ∨ p ∣ 498 then 1 else 2 :=
  nu_p_evenPair (by decide : (498 : ℕ) ≠ 0) (by decide : Even 498) hp

theorem nu_p_fiveHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 500) p = if p = 2 ∨ p ∣ 500 then 1 else 2 :=
  nu_p_evenPair (by decide : (500 : ℕ) ≠ 0) (by decide : Even 500) hp

theorem nu_p_fourHundredNinetyTwo_two : nu_p (evenPair 492) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 492)

theorem localFactor_fourHundredNinetyTwo_two : localFactor (evenPair 492) 2 = 2 :=
  localFactor_evenPair_two (by decide : (492 : ℕ) ≠ 0) (by decide : Even 492)

theorem nu_p_fiveHundred_two : nu_p (evenPair 500) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 500)

theorem localFactor_fiveHundred_two : localFactor (evenPair 500) 2 = 2 :=
  localFactor_evenPair_two (by decide : (500 : ℕ) ≠ 0) (by decide : Even 500)

end Brockian.SingularSeries.Gaps492500
