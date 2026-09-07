/-
  Brockian/SingularSeriesGaps12721280.lean — even binary gaps n ∈ {1272, 1274, 1276, 1278, 1280}.

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

namespace Brockian.SingularSeries.Gaps12721280

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredSeventyTwo : (evenPair 1272).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1272 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSeventyFour : (evenPair 1274).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1274 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSeventySix : (evenPair 1276).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1276 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSeventyEight : (evenPair 1278).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1278 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredEighty : (evenPair 1280).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1280 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredSeventyTwo : IsAdmissible (evenPair 1272) :=
  isAdmissible_evenPair (by decide : Even 1272)

theorem isAdmissible_evenPair_oneThousandTwoHundredSeventyFour : IsAdmissible (evenPair 1274) :=
  isAdmissible_evenPair (by decide : Even 1274)

theorem isAdmissible_evenPair_oneThousandTwoHundredSeventySix : IsAdmissible (evenPair 1276) :=
  isAdmissible_evenPair (by decide : Even 1276)

theorem isAdmissible_evenPair_oneThousandTwoHundredSeventyEight : IsAdmissible (evenPair 1278) :=
  isAdmissible_evenPair (by decide : Even 1278)

theorem isAdmissible_evenPair_oneThousandTwoHundredEighty : IsAdmissible (evenPair 1280) :=
  isAdmissible_evenPair (by decide : Even 1280)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSeventyTwo : 0 < singularSeries (evenPair 1272) :=
  singular_series_pos_evenPair (by decide : Even 1272)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSeventyFour : 0 < singularSeries (evenPair 1274) :=
  singular_series_pos_evenPair (by decide : Even 1274)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSeventySix : 0 < singularSeries (evenPair 1276) :=
  singular_series_pos_evenPair (by decide : Even 1276)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSeventyEight : 0 < singularSeries (evenPair 1278) :=
  singular_series_pos_evenPair (by decide : Even 1278)

theorem singular_series_pos_evenPair_oneThousandTwoHundredEighty : 0 < singularSeries (evenPair 1280) :=
  singular_series_pos_evenPair (by decide : Even 1280)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1272) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1272) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1274) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1274) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1276) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1276) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1278) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1278) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1280) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1280) P

theorem nu_p_oneThousandTwoHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1272) p = if p = 2 ∨ p ∣ 1272 then 1 else 2 :=
  nu_p_evenPair (by decide : (1272 : ℕ) ≠ 0) (by decide : Even 1272) hp

theorem nu_p_oneThousandTwoHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1274) p = if p = 2 ∨ p ∣ 1274 then 1 else 2 :=
  nu_p_evenPair (by decide : (1274 : ℕ) ≠ 0) (by decide : Even 1274) hp

theorem nu_p_oneThousandTwoHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1276) p = if p = 2 ∨ p ∣ 1276 then 1 else 2 :=
  nu_p_evenPair (by decide : (1276 : ℕ) ≠ 0) (by decide : Even 1276) hp

theorem nu_p_oneThousandTwoHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1278) p = if p = 2 ∨ p ∣ 1278 then 1 else 2 :=
  nu_p_evenPair (by decide : (1278 : ℕ) ≠ 0) (by decide : Even 1278) hp

theorem nu_p_oneThousandTwoHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1280) p = if p = 2 ∨ p ∣ 1280 then 1 else 2 :=
  nu_p_evenPair (by decide : (1280 : ℕ) ≠ 0) (by decide : Even 1280) hp

theorem nu_p_oneThousandTwoHundredSeventyTwo_two : nu_p (evenPair 1272) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1272)

theorem localFactor_oneThousandTwoHundredSeventyTwo_two : localFactor (evenPair 1272) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1272 : ℕ) ≠ 0) (by decide : Even 1272)

theorem nu_p_oneThousandTwoHundredEighty_two : nu_p (evenPair 1280) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1280)

theorem localFactor_oneThousandTwoHundredEighty_two : localFactor (evenPair 1280) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1280 : ℕ) ≠ 0) (by decide : Even 1280)

end Brockian.SingularSeries.Gaps12721280
