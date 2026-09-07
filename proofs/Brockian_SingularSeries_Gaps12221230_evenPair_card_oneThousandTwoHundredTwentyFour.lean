/-
  Brockian/SingularSeriesGaps12221230.lean — even binary gaps n ∈ {1222, 1224, 1226, 1228, 1230}.

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

namespace Brockian.SingularSeries.Gaps12221230

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredTwentyTwo : (evenPair 1222).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1222 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredTwentyFour : (evenPair 1224).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1224 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredTwentySix : (evenPair 1226).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1226 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredTwentyEight : (evenPair 1228).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1228 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredThirty : (evenPair 1230).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1230 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredTwentyTwo : IsAdmissible (evenPair 1222) :=
  isAdmissible_evenPair (by decide : Even 1222)

theorem isAdmissible_evenPair_oneThousandTwoHundredTwentyFour : IsAdmissible (evenPair 1224) :=
  isAdmissible_evenPair (by decide : Even 1224)

theorem isAdmissible_evenPair_oneThousandTwoHundredTwentySix : IsAdmissible (evenPair 1226) :=
  isAdmissible_evenPair (by decide : Even 1226)

theorem isAdmissible_evenPair_oneThousandTwoHundredTwentyEight : IsAdmissible (evenPair 1228) :=
  isAdmissible_evenPair (by decide : Even 1228)

theorem isAdmissible_evenPair_oneThousandTwoHundredThirty : IsAdmissible (evenPair 1230) :=
  isAdmissible_evenPair (by decide : Even 1230)

theorem singular_series_pos_evenPair_oneThousandTwoHundredTwentyTwo : 0 < singularSeries (evenPair 1222) :=
  singular_series_pos_evenPair (by decide : Even 1222)

theorem singular_series_pos_evenPair_oneThousandTwoHundredTwentyFour : 0 < singularSeries (evenPair 1224) :=
  singular_series_pos_evenPair (by decide : Even 1224)

theorem singular_series_pos_evenPair_oneThousandTwoHundredTwentySix : 0 < singularSeries (evenPair 1226) :=
  singular_series_pos_evenPair (by decide : Even 1226)

theorem singular_series_pos_evenPair_oneThousandTwoHundredTwentyEight : 0 < singularSeries (evenPair 1228) :=
  singular_series_pos_evenPair (by decide : Even 1228)

theorem singular_series_pos_evenPair_oneThousandTwoHundredThirty : 0 < singularSeries (evenPair 1230) :=
  singular_series_pos_evenPair (by decide : Even 1230)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1222) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1222) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1224) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1224) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1226) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1226) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1228) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1228) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1230) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1230) P

theorem nu_p_oneThousandTwoHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1222) p = if p = 2 ∨ p ∣ 1222 then 1 else 2 :=
  nu_p_evenPair (by decide : (1222 : ℕ) ≠ 0) (by decide : Even 1222) hp

theorem nu_p_oneThousandTwoHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1224) p = if p = 2 ∨ p ∣ 1224 then 1 else 2 :=
  nu_p_evenPair (by decide : (1224 : ℕ) ≠ 0) (by decide : Even 1224) hp

theorem nu_p_oneThousandTwoHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1226) p = if p = 2 ∨ p ∣ 1226 then 1 else 2 :=
  nu_p_evenPair (by decide : (1226 : ℕ) ≠ 0) (by decide : Even 1226) hp

theorem nu_p_oneThousandTwoHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1228) p = if p = 2 ∨ p ∣ 1228 then 1 else 2 :=
  nu_p_evenPair (by decide : (1228 : ℕ) ≠ 0) (by decide : Even 1228) hp

theorem nu_p_oneThousandTwoHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1230) p = if p = 2 ∨ p ∣ 1230 then 1 else 2 :=
  nu_p_evenPair (by decide : (1230 : ℕ) ≠ 0) (by decide : Even 1230) hp

theorem nu_p_oneThousandTwoHundredTwentyTwo_two : nu_p (evenPair 1222) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1222)

theorem localFactor_oneThousandTwoHundredTwentyTwo_two : localFactor (evenPair 1222) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1222 : ℕ) ≠ 0) (by decide : Even 1222)

theorem nu_p_oneThousandTwoHundredThirty_two : nu_p (evenPair 1230) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1230)

theorem localFactor_oneThousandTwoHundredThirty_two : localFactor (evenPair 1230) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1230 : ℕ) ≠ 0) (by decide : Even 1230)

end Brockian.SingularSeries.Gaps12221230
