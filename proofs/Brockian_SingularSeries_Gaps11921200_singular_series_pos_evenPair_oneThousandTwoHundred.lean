/-
  Brockian/SingularSeriesGaps11921200.lean — even binary gaps n ∈ {1192, 1194, 1196, 1198, 1200}.

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

namespace Brockian.SingularSeries.Gaps11921200

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredNinetyTwo : (evenPair 1192).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1192 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredNinetyFour : (evenPair 1194).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1194 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredNinetySix : (evenPair 1196).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1196 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredNinetyEight : (evenPair 1198).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1198 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundred : (evenPair 1200).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1200 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredNinetyTwo : IsAdmissible (evenPair 1192) :=
  isAdmissible_evenPair (by decide : Even 1192)

theorem isAdmissible_evenPair_oneThousandOneHundredNinetyFour : IsAdmissible (evenPair 1194) :=
  isAdmissible_evenPair (by decide : Even 1194)

theorem isAdmissible_evenPair_oneThousandOneHundredNinetySix : IsAdmissible (evenPair 1196) :=
  isAdmissible_evenPair (by decide : Even 1196)

theorem isAdmissible_evenPair_oneThousandOneHundredNinetyEight : IsAdmissible (evenPair 1198) :=
  isAdmissible_evenPair (by decide : Even 1198)

theorem isAdmissible_evenPair_oneThousandTwoHundred : IsAdmissible (evenPair 1200) :=
  isAdmissible_evenPair (by decide : Even 1200)

theorem singular_series_pos_evenPair_oneThousandOneHundredNinetyTwo : 0 < singularSeries (evenPair 1192) :=
  singular_series_pos_evenPair (by decide : Even 1192)

theorem singular_series_pos_evenPair_oneThousandOneHundredNinetyFour : 0 < singularSeries (evenPair 1194) :=
  singular_series_pos_evenPair (by decide : Even 1194)

theorem singular_series_pos_evenPair_oneThousandOneHundredNinetySix : 0 < singularSeries (evenPair 1196) :=
  singular_series_pos_evenPair (by decide : Even 1196)

theorem singular_series_pos_evenPair_oneThousandOneHundredNinetyEight : 0 < singularSeries (evenPair 1198) :=
  singular_series_pos_evenPair (by decide : Even 1198)

theorem singular_series_pos_evenPair_oneThousandTwoHundred : 0 < singularSeries (evenPair 1200) :=
  singular_series_pos_evenPair (by decide : Even 1200)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1192) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1192) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1194) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1194) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1196) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1196) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1198) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1198) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1200) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1200) P

theorem nu_p_oneThousandOneHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1192) p = if p = 2 ∨ p ∣ 1192 then 1 else 2 :=
  nu_p_evenPair (by decide : (1192 : ℕ) ≠ 0) (by decide : Even 1192) hp

theorem nu_p_oneThousandOneHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1194) p = if p = 2 ∨ p ∣ 1194 then 1 else 2 :=
  nu_p_evenPair (by decide : (1194 : ℕ) ≠ 0) (by decide : Even 1194) hp

theorem nu_p_oneThousandOneHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1196) p = if p = 2 ∨ p ∣ 1196 then 1 else 2 :=
  nu_p_evenPair (by decide : (1196 : ℕ) ≠ 0) (by decide : Even 1196) hp

theorem nu_p_oneThousandOneHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1198) p = if p = 2 ∨ p ∣ 1198 then 1 else 2 :=
  nu_p_evenPair (by decide : (1198 : ℕ) ≠ 0) (by decide : Even 1198) hp

theorem nu_p_oneThousandTwoHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1200) p = if p = 2 ∨ p ∣ 1200 then 1 else 2 :=
  nu_p_evenPair (by decide : (1200 : ℕ) ≠ 0) (by decide : Even 1200) hp

theorem nu_p_oneThousandOneHundredNinetyTwo_two : nu_p (evenPair 1192) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1192)

theorem localFactor_oneThousandOneHundredNinetyTwo_two : localFactor (evenPair 1192) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1192 : ℕ) ≠ 0) (by decide : Even 1192)

theorem nu_p_oneThousandTwoHundred_two : nu_p (evenPair 1200) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1200)

theorem localFactor_oneThousandTwoHundred_two : localFactor (evenPair 1200) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1200 : ℕ) ≠ 0) (by decide : Even 1200)

end Brockian.SingularSeries.Gaps11921200
