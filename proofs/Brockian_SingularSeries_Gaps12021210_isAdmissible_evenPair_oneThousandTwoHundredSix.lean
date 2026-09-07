/-
  Brockian/SingularSeriesGaps12021210.lean — even binary gaps n ∈ {1202, 1204, 1206, 1208, 1210}.

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

namespace Brockian.SingularSeries.Gaps12021210

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredTwo : (evenPair 1202).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1202 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredFour : (evenPair 1204).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1204 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSix : (evenPair 1206).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1206 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredEight : (evenPair 1208).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1208 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredTen : (evenPair 1210).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1210 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredTwo : IsAdmissible (evenPair 1202) :=
  isAdmissible_evenPair (by decide : Even 1202)

theorem isAdmissible_evenPair_oneThousandTwoHundredFour : IsAdmissible (evenPair 1204) :=
  isAdmissible_evenPair (by decide : Even 1204)

theorem isAdmissible_evenPair_oneThousandTwoHundredSix : IsAdmissible (evenPair 1206) :=
  isAdmissible_evenPair (by decide : Even 1206)

theorem isAdmissible_evenPair_oneThousandTwoHundredEight : IsAdmissible (evenPair 1208) :=
  isAdmissible_evenPair (by decide : Even 1208)

theorem isAdmissible_evenPair_oneThousandTwoHundredTen : IsAdmissible (evenPair 1210) :=
  isAdmissible_evenPair (by decide : Even 1210)

theorem singular_series_pos_evenPair_oneThousandTwoHundredTwo : 0 < singularSeries (evenPair 1202) :=
  singular_series_pos_evenPair (by decide : Even 1202)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFour : 0 < singularSeries (evenPair 1204) :=
  singular_series_pos_evenPair (by decide : Even 1204)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSix : 0 < singularSeries (evenPair 1206) :=
  singular_series_pos_evenPair (by decide : Even 1206)

theorem singular_series_pos_evenPair_oneThousandTwoHundredEight : 0 < singularSeries (evenPair 1208) :=
  singular_series_pos_evenPair (by decide : Even 1208)

theorem singular_series_pos_evenPair_oneThousandTwoHundredTen : 0 < singularSeries (evenPair 1210) :=
  singular_series_pos_evenPair (by decide : Even 1210)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1202) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1202) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1204) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1204) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1206) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1206) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1208) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1208) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1210) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1210) P

theorem nu_p_oneThousandTwoHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1202) p = if p = 2 ∨ p ∣ 1202 then 1 else 2 :=
  nu_p_evenPair (by decide : (1202 : ℕ) ≠ 0) (by decide : Even 1202) hp

theorem nu_p_oneThousandTwoHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1204) p = if p = 2 ∨ p ∣ 1204 then 1 else 2 :=
  nu_p_evenPair (by decide : (1204 : ℕ) ≠ 0) (by decide : Even 1204) hp

theorem nu_p_oneThousandTwoHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1206) p = if p = 2 ∨ p ∣ 1206 then 1 else 2 :=
  nu_p_evenPair (by decide : (1206 : ℕ) ≠ 0) (by decide : Even 1206) hp

theorem nu_p_oneThousandTwoHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1208) p = if p = 2 ∨ p ∣ 1208 then 1 else 2 :=
  nu_p_evenPair (by decide : (1208 : ℕ) ≠ 0) (by decide : Even 1208) hp

theorem nu_p_oneThousandTwoHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1210) p = if p = 2 ∨ p ∣ 1210 then 1 else 2 :=
  nu_p_evenPair (by decide : (1210 : ℕ) ≠ 0) (by decide : Even 1210) hp

theorem nu_p_oneThousandTwoHundredTwo_two : nu_p (evenPair 1202) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1202)

theorem localFactor_oneThousandTwoHundredTwo_two : localFactor (evenPair 1202) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1202 : ℕ) ≠ 0) (by decide : Even 1202)

theorem nu_p_oneThousandTwoHundredTen_two : nu_p (evenPair 1210) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1210)

theorem localFactor_oneThousandTwoHundredTen_two : localFactor (evenPair 1210) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1210 : ℕ) ≠ 0) (by decide : Even 1210)

end Brockian.SingularSeries.Gaps12021210
