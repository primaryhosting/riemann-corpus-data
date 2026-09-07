/-
  Brockian/SingularSeriesGaps12521260.lean — even binary gaps n ∈ {1252, 1254, 1256, 1258, 1260}.

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

namespace Brockian.SingularSeries.Gaps12521260

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredFiftyTwo : (evenPair 1252).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1252 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredFiftyFour : (evenPair 1254).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1254 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredFiftySix : (evenPair 1256).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1256 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredFiftyEight : (evenPair 1258).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1258 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSixty : (evenPair 1260).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1260 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredFiftyTwo : IsAdmissible (evenPair 1252) :=
  isAdmissible_evenPair (by decide : Even 1252)

theorem isAdmissible_evenPair_oneThousandTwoHundredFiftyFour : IsAdmissible (evenPair 1254) :=
  isAdmissible_evenPair (by decide : Even 1254)

theorem isAdmissible_evenPair_oneThousandTwoHundredFiftySix : IsAdmissible (evenPair 1256) :=
  isAdmissible_evenPair (by decide : Even 1256)

theorem isAdmissible_evenPair_oneThousandTwoHundredFiftyEight : IsAdmissible (evenPair 1258) :=
  isAdmissible_evenPair (by decide : Even 1258)

theorem isAdmissible_evenPair_oneThousandTwoHundredSixty : IsAdmissible (evenPair 1260) :=
  isAdmissible_evenPair (by decide : Even 1260)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFiftyTwo : 0 < singularSeries (evenPair 1252) :=
  singular_series_pos_evenPair (by decide : Even 1252)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFiftyFour : 0 < singularSeries (evenPair 1254) :=
  singular_series_pos_evenPair (by decide : Even 1254)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFiftySix : 0 < singularSeries (evenPair 1256) :=
  singular_series_pos_evenPair (by decide : Even 1256)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFiftyEight : 0 < singularSeries (evenPair 1258) :=
  singular_series_pos_evenPair (by decide : Even 1258)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSixty : 0 < singularSeries (evenPair 1260) :=
  singular_series_pos_evenPair (by decide : Even 1260)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1252) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1252) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1254) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1254) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1256) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1256) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1258) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1258) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1260) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1260) P

theorem nu_p_oneThousandTwoHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1252) p = if p = 2 ∨ p ∣ 1252 then 1 else 2 :=
  nu_p_evenPair (by decide : (1252 : ℕ) ≠ 0) (by decide : Even 1252) hp

theorem nu_p_oneThousandTwoHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1254) p = if p = 2 ∨ p ∣ 1254 then 1 else 2 :=
  nu_p_evenPair (by decide : (1254 : ℕ) ≠ 0) (by decide : Even 1254) hp

theorem nu_p_oneThousandTwoHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1256) p = if p = 2 ∨ p ∣ 1256 then 1 else 2 :=
  nu_p_evenPair (by decide : (1256 : ℕ) ≠ 0) (by decide : Even 1256) hp

theorem nu_p_oneThousandTwoHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1258) p = if p = 2 ∨ p ∣ 1258 then 1 else 2 :=
  nu_p_evenPair (by decide : (1258 : ℕ) ≠ 0) (by decide : Even 1258) hp

theorem nu_p_oneThousandTwoHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1260) p = if p = 2 ∨ p ∣ 1260 then 1 else 2 :=
  nu_p_evenPair (by decide : (1260 : ℕ) ≠ 0) (by decide : Even 1260) hp

theorem nu_p_oneThousandTwoHundredFiftyTwo_two : nu_p (evenPair 1252) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1252)

theorem localFactor_oneThousandTwoHundredFiftyTwo_two : localFactor (evenPair 1252) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1252 : ℕ) ≠ 0) (by decide : Even 1252)

theorem nu_p_oneThousandTwoHundredSixty_two : nu_p (evenPair 1260) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1260)

theorem localFactor_oneThousandTwoHundredSixty_two : localFactor (evenPair 1260) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1260 : ℕ) ≠ 0) (by decide : Even 1260)

end Brockian.SingularSeries.Gaps12521260
