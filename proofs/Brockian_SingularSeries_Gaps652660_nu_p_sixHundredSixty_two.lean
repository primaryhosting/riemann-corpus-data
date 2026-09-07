/-
  Brockian/SingularSeriesGaps652660.lean — even binary gaps n ∈ {652, 654, 656, 658, 660}.

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

namespace Brockian.SingularSeries.Gaps652660

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredFiftyTwo : (evenPair 652).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (652 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredFiftyFour : (evenPair 654).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (654 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredFiftySix : (evenPair 656).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (656 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredFiftyEight : (evenPair 658).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (658 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSixty : (evenPair 660).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (660 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredFiftyTwo : IsAdmissible (evenPair 652) :=
  isAdmissible_evenPair (by decide : Even 652)

theorem isAdmissible_evenPair_sixHundredFiftyFour : IsAdmissible (evenPair 654) :=
  isAdmissible_evenPair (by decide : Even 654)

theorem isAdmissible_evenPair_sixHundredFiftySix : IsAdmissible (evenPair 656) :=
  isAdmissible_evenPair (by decide : Even 656)

theorem isAdmissible_evenPair_sixHundredFiftyEight : IsAdmissible (evenPair 658) :=
  isAdmissible_evenPair (by decide : Even 658)

theorem isAdmissible_evenPair_sixHundredSixty : IsAdmissible (evenPair 660) :=
  isAdmissible_evenPair (by decide : Even 660)

theorem singular_series_pos_evenPair_sixHundredFiftyTwo : 0 < singularSeries (evenPair 652) :=
  singular_series_pos_evenPair (by decide : Even 652)

theorem singular_series_pos_evenPair_sixHundredFiftyFour : 0 < singularSeries (evenPair 654) :=
  singular_series_pos_evenPair (by decide : Even 654)

theorem singular_series_pos_evenPair_sixHundredFiftySix : 0 < singularSeries (evenPair 656) :=
  singular_series_pos_evenPair (by decide : Even 656)

theorem singular_series_pos_evenPair_sixHundredFiftyEight : 0 < singularSeries (evenPair 658) :=
  singular_series_pos_evenPair (by decide : Even 658)

theorem singular_series_pos_evenPair_sixHundredSixty : 0 < singularSeries (evenPair 660) :=
  singular_series_pos_evenPair (by decide : Even 660)

theorem singular_series_finite_pos_evenPair_sixHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 652) P :=
  singular_series_finite_pos_evenPair (by decide : Even 652) P

theorem singular_series_finite_pos_evenPair_sixHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 654) P :=
  singular_series_finite_pos_evenPair (by decide : Even 654) P

theorem singular_series_finite_pos_evenPair_sixHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 656) P :=
  singular_series_finite_pos_evenPair (by decide : Even 656) P

theorem singular_series_finite_pos_evenPair_sixHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 658) P :=
  singular_series_finite_pos_evenPair (by decide : Even 658) P

theorem singular_series_finite_pos_evenPair_sixHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 660) P :=
  singular_series_finite_pos_evenPair (by decide : Even 660) P

theorem nu_p_sixHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 652) p = if p = 2 ∨ p ∣ 652 then 1 else 2 :=
  nu_p_evenPair (by decide : (652 : ℕ) ≠ 0) (by decide : Even 652) hp

theorem nu_p_sixHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 654) p = if p = 2 ∨ p ∣ 654 then 1 else 2 :=
  nu_p_evenPair (by decide : (654 : ℕ) ≠ 0) (by decide : Even 654) hp

theorem nu_p_sixHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 656) p = if p = 2 ∨ p ∣ 656 then 1 else 2 :=
  nu_p_evenPair (by decide : (656 : ℕ) ≠ 0) (by decide : Even 656) hp

theorem nu_p_sixHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 658) p = if p = 2 ∨ p ∣ 658 then 1 else 2 :=
  nu_p_evenPair (by decide : (658 : ℕ) ≠ 0) (by decide : Even 658) hp

theorem nu_p_sixHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 660) p = if p = 2 ∨ p ∣ 660 then 1 else 2 :=
  nu_p_evenPair (by decide : (660 : ℕ) ≠ 0) (by decide : Even 660) hp

theorem nu_p_sixHundredFiftyTwo_two : nu_p (evenPair 652) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 652)

theorem localFactor_sixHundredFiftyTwo_two : localFactor (evenPair 652) 2 = 2 :=
  localFactor_evenPair_two (by decide : (652 : ℕ) ≠ 0) (by decide : Even 652)

theorem nu_p_sixHundredSixty_two : nu_p (evenPair 660) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 660)

theorem localFactor_sixHundredSixty_two : localFactor (evenPair 660) 2 = 2 :=
  localFactor_evenPair_two (by decide : (660 : ℕ) ≠ 0) (by decide : Even 660)

end Brockian.SingularSeries.Gaps652660
