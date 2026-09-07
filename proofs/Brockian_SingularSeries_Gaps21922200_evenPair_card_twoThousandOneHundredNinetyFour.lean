/-
  Brockian/SingularSeriesGaps21922200.lean — even binary gaps n ∈ {2192, 2194, 2196, 2198, 2200}.

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

namespace Brockian.SingularSeries.Gaps21922200

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredNinetyTwo : (evenPair 2192).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2192 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredNinetyFour : (evenPair 2194).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2194 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredNinetySix : (evenPair 2196).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2196 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredNinetyEight : (evenPair 2198).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2198 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandTwoHundred : (evenPair 2200).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2200 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredNinetyTwo : IsAdmissible (evenPair 2192) :=
  isAdmissible_evenPair (by decide : Even 2192)

theorem isAdmissible_evenPair_twoThousandOneHundredNinetyFour : IsAdmissible (evenPair 2194) :=
  isAdmissible_evenPair (by decide : Even 2194)

theorem isAdmissible_evenPair_twoThousandOneHundredNinetySix : IsAdmissible (evenPair 2196) :=
  isAdmissible_evenPair (by decide : Even 2196)

theorem isAdmissible_evenPair_twoThousandOneHundredNinetyEight : IsAdmissible (evenPair 2198) :=
  isAdmissible_evenPair (by decide : Even 2198)

theorem isAdmissible_evenPair_twoThousandTwoHundred : IsAdmissible (evenPair 2200) :=
  isAdmissible_evenPair (by decide : Even 2200)

theorem singular_series_pos_evenPair_twoThousandOneHundredNinetyTwo : 0 < singularSeries (evenPair 2192) :=
  singular_series_pos_evenPair (by decide : Even 2192)

theorem singular_series_pos_evenPair_twoThousandOneHundredNinetyFour : 0 < singularSeries (evenPair 2194) :=
  singular_series_pos_evenPair (by decide : Even 2194)

theorem singular_series_pos_evenPair_twoThousandOneHundredNinetySix : 0 < singularSeries (evenPair 2196) :=
  singular_series_pos_evenPair (by decide : Even 2196)

theorem singular_series_pos_evenPair_twoThousandOneHundredNinetyEight : 0 < singularSeries (evenPair 2198) :=
  singular_series_pos_evenPair (by decide : Even 2198)

theorem singular_series_pos_evenPair_twoThousandTwoHundred : 0 < singularSeries (evenPair 2200) :=
  singular_series_pos_evenPair (by decide : Even 2200)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2192) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2192) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2194) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2194) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2196) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2196) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2198) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2198) P

theorem singular_series_finite_pos_evenPair_twoThousandTwoHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2200) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2200) P

theorem nu_p_twoThousandOneHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2192) p = if p = 2 ∨ p ∣ 2192 then 1 else 2 :=
  nu_p_evenPair (by decide : (2192 : ℕ) ≠ 0) (by decide : Even 2192) hp

theorem nu_p_twoThousandOneHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2194) p = if p = 2 ∨ p ∣ 2194 then 1 else 2 :=
  nu_p_evenPair (by decide : (2194 : ℕ) ≠ 0) (by decide : Even 2194) hp

theorem nu_p_twoThousandOneHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2196) p = if p = 2 ∨ p ∣ 2196 then 1 else 2 :=
  nu_p_evenPair (by decide : (2196 : ℕ) ≠ 0) (by decide : Even 2196) hp

theorem nu_p_twoThousandOneHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2198) p = if p = 2 ∨ p ∣ 2198 then 1 else 2 :=
  nu_p_evenPair (by decide : (2198 : ℕ) ≠ 0) (by decide : Even 2198) hp

theorem nu_p_twoThousandTwoHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2200) p = if p = 2 ∨ p ∣ 2200 then 1 else 2 :=
  nu_p_evenPair (by decide : (2200 : ℕ) ≠ 0) (by decide : Even 2200) hp

theorem nu_p_twoThousandOneHundredNinetyTwo_two : nu_p (evenPair 2192) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2192)

theorem localFactor_twoThousandOneHundredNinetyTwo_two : localFactor (evenPair 2192) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2192 : ℕ) ≠ 0) (by decide : Even 2192)

theorem nu_p_twoThousandTwoHundred_two : nu_p (evenPair 2200) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2200)

theorem localFactor_twoThousandTwoHundred_two : localFactor (evenPair 2200) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2200 : ℕ) ≠ 0) (by decide : Even 2200)

end Brockian.SingularSeries.Gaps21922200
