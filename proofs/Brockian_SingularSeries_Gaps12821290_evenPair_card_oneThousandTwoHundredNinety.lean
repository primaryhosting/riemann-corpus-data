/-
  Brockian/SingularSeriesGaps12821290.lean — even binary gaps n ∈ {1282, 1284, 1286, 1288, 1290}.

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

namespace Brockian.SingularSeries.Gaps12821290

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredEightyTwo : (evenPair 1282).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1282 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredEightyFour : (evenPair 1284).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1284 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredEightySix : (evenPair 1286).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1286 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredEightyEight : (evenPair 1288).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1288 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredNinety : (evenPair 1290).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1290 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredEightyTwo : IsAdmissible (evenPair 1282) :=
  isAdmissible_evenPair (by decide : Even 1282)

theorem isAdmissible_evenPair_oneThousandTwoHundredEightyFour : IsAdmissible (evenPair 1284) :=
  isAdmissible_evenPair (by decide : Even 1284)

theorem isAdmissible_evenPair_oneThousandTwoHundredEightySix : IsAdmissible (evenPair 1286) :=
  isAdmissible_evenPair (by decide : Even 1286)

theorem isAdmissible_evenPair_oneThousandTwoHundredEightyEight : IsAdmissible (evenPair 1288) :=
  isAdmissible_evenPair (by decide : Even 1288)

theorem isAdmissible_evenPair_oneThousandTwoHundredNinety : IsAdmissible (evenPair 1290) :=
  isAdmissible_evenPair (by decide : Even 1290)

theorem singular_series_pos_evenPair_oneThousandTwoHundredEightyTwo : 0 < singularSeries (evenPair 1282) :=
  singular_series_pos_evenPair (by decide : Even 1282)

theorem singular_series_pos_evenPair_oneThousandTwoHundredEightyFour : 0 < singularSeries (evenPair 1284) :=
  singular_series_pos_evenPair (by decide : Even 1284)

theorem singular_series_pos_evenPair_oneThousandTwoHundredEightySix : 0 < singularSeries (evenPair 1286) :=
  singular_series_pos_evenPair (by decide : Even 1286)

theorem singular_series_pos_evenPair_oneThousandTwoHundredEightyEight : 0 < singularSeries (evenPair 1288) :=
  singular_series_pos_evenPair (by decide : Even 1288)

theorem singular_series_pos_evenPair_oneThousandTwoHundredNinety : 0 < singularSeries (evenPair 1290) :=
  singular_series_pos_evenPair (by decide : Even 1290)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1282) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1282) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1284) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1284) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1286) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1286) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1288) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1288) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1290) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1290) P

theorem nu_p_oneThousandTwoHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1282) p = if p = 2 ∨ p ∣ 1282 then 1 else 2 :=
  nu_p_evenPair (by decide : (1282 : ℕ) ≠ 0) (by decide : Even 1282) hp

theorem nu_p_oneThousandTwoHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1284) p = if p = 2 ∨ p ∣ 1284 then 1 else 2 :=
  nu_p_evenPair (by decide : (1284 : ℕ) ≠ 0) (by decide : Even 1284) hp

theorem nu_p_oneThousandTwoHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1286) p = if p = 2 ∨ p ∣ 1286 then 1 else 2 :=
  nu_p_evenPair (by decide : (1286 : ℕ) ≠ 0) (by decide : Even 1286) hp

theorem nu_p_oneThousandTwoHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1288) p = if p = 2 ∨ p ∣ 1288 then 1 else 2 :=
  nu_p_evenPair (by decide : (1288 : ℕ) ≠ 0) (by decide : Even 1288) hp

theorem nu_p_oneThousandTwoHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1290) p = if p = 2 ∨ p ∣ 1290 then 1 else 2 :=
  nu_p_evenPair (by decide : (1290 : ℕ) ≠ 0) (by decide : Even 1290) hp

theorem nu_p_oneThousandTwoHundredEightyTwo_two : nu_p (evenPair 1282) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1282)

theorem localFactor_oneThousandTwoHundredEightyTwo_two : localFactor (evenPair 1282) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1282 : ℕ) ≠ 0) (by decide : Even 1282)

theorem nu_p_oneThousandTwoHundredNinety_two : nu_p (evenPair 1290) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1290)

theorem localFactor_oneThousandTwoHundredNinety_two : localFactor (evenPair 1290) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1290 : ℕ) ≠ 0) (by decide : Even 1290)

end Brockian.SingularSeries.Gaps12821290
