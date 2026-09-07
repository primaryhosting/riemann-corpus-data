/-
  Brockian/SingularSeriesGaps12621270.lean — even binary gaps n ∈ {1262, 1264, 1266, 1268, 1270}.

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

namespace Brockian.SingularSeries.Gaps12621270

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredSixtyTwo : (evenPair 1262).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1262 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSixtyFour : (evenPair 1264).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1264 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSixtySix : (evenPair 1266).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1266 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSixtyEight : (evenPair 1268).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1268 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredSeventy : (evenPair 1270).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1270 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredSixtyTwo : IsAdmissible (evenPair 1262) :=
  isAdmissible_evenPair (by decide : Even 1262)

theorem isAdmissible_evenPair_oneThousandTwoHundredSixtyFour : IsAdmissible (evenPair 1264) :=
  isAdmissible_evenPair (by decide : Even 1264)

theorem isAdmissible_evenPair_oneThousandTwoHundredSixtySix : IsAdmissible (evenPair 1266) :=
  isAdmissible_evenPair (by decide : Even 1266)

theorem isAdmissible_evenPair_oneThousandTwoHundredSixtyEight : IsAdmissible (evenPair 1268) :=
  isAdmissible_evenPair (by decide : Even 1268)

theorem isAdmissible_evenPair_oneThousandTwoHundredSeventy : IsAdmissible (evenPair 1270) :=
  isAdmissible_evenPair (by decide : Even 1270)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSixtyTwo : 0 < singularSeries (evenPair 1262) :=
  singular_series_pos_evenPair (by decide : Even 1262)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSixtyFour : 0 < singularSeries (evenPair 1264) :=
  singular_series_pos_evenPair (by decide : Even 1264)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSixtySix : 0 < singularSeries (evenPair 1266) :=
  singular_series_pos_evenPair (by decide : Even 1266)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSixtyEight : 0 < singularSeries (evenPair 1268) :=
  singular_series_pos_evenPair (by decide : Even 1268)

theorem singular_series_pos_evenPair_oneThousandTwoHundredSeventy : 0 < singularSeries (evenPair 1270) :=
  singular_series_pos_evenPair (by decide : Even 1270)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1262) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1262) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1264) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1264) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1266) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1266) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1268) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1268) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1270) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1270) P

theorem nu_p_oneThousandTwoHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1262) p = if p = 2 ∨ p ∣ 1262 then 1 else 2 :=
  nu_p_evenPair (by decide : (1262 : ℕ) ≠ 0) (by decide : Even 1262) hp

theorem nu_p_oneThousandTwoHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1264) p = if p = 2 ∨ p ∣ 1264 then 1 else 2 :=
  nu_p_evenPair (by decide : (1264 : ℕ) ≠ 0) (by decide : Even 1264) hp

theorem nu_p_oneThousandTwoHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1266) p = if p = 2 ∨ p ∣ 1266 then 1 else 2 :=
  nu_p_evenPair (by decide : (1266 : ℕ) ≠ 0) (by decide : Even 1266) hp

theorem nu_p_oneThousandTwoHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1268) p = if p = 2 ∨ p ∣ 1268 then 1 else 2 :=
  nu_p_evenPair (by decide : (1268 : ℕ) ≠ 0) (by decide : Even 1268) hp

theorem nu_p_oneThousandTwoHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1270) p = if p = 2 ∨ p ∣ 1270 then 1 else 2 :=
  nu_p_evenPair (by decide : (1270 : ℕ) ≠ 0) (by decide : Even 1270) hp

theorem nu_p_oneThousandTwoHundredSixtyTwo_two : nu_p (evenPair 1262) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1262)

theorem localFactor_oneThousandTwoHundredSixtyTwo_two : localFactor (evenPair 1262) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1262 : ℕ) ≠ 0) (by decide : Even 1262)

theorem nu_p_oneThousandTwoHundredSeventy_two : nu_p (evenPair 1270) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1270)

theorem localFactor_oneThousandTwoHundredSeventy_two : localFactor (evenPair 1270) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1270 : ℕ) ≠ 0) (by decide : Even 1270)

end Brockian.SingularSeries.Gaps12621270
