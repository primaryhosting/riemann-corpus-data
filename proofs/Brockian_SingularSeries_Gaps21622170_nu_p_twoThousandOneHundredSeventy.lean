/-
  Brockian/SingularSeriesGaps21622170.lean — even binary gaps n ∈ {2162, 2164, 2166, 2168, 2170}.

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

namespace Brockian.SingularSeries.Gaps21622170

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredSixtyTwo : (evenPair 2162).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2162 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSixtyFour : (evenPair 2164).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2164 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSixtySix : (evenPair 2166).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2166 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSixtyEight : (evenPair 2168).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2168 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSeventy : (evenPair 2170).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2170 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredSixtyTwo : IsAdmissible (evenPair 2162) :=
  isAdmissible_evenPair (by decide : Even 2162)

theorem isAdmissible_evenPair_twoThousandOneHundredSixtyFour : IsAdmissible (evenPair 2164) :=
  isAdmissible_evenPair (by decide : Even 2164)

theorem isAdmissible_evenPair_twoThousandOneHundredSixtySix : IsAdmissible (evenPair 2166) :=
  isAdmissible_evenPair (by decide : Even 2166)

theorem isAdmissible_evenPair_twoThousandOneHundredSixtyEight : IsAdmissible (evenPair 2168) :=
  isAdmissible_evenPair (by decide : Even 2168)

theorem isAdmissible_evenPair_twoThousandOneHundredSeventy : IsAdmissible (evenPair 2170) :=
  isAdmissible_evenPair (by decide : Even 2170)

theorem singular_series_pos_evenPair_twoThousandOneHundredSixtyTwo : 0 < singularSeries (evenPair 2162) :=
  singular_series_pos_evenPair (by decide : Even 2162)

theorem singular_series_pos_evenPair_twoThousandOneHundredSixtyFour : 0 < singularSeries (evenPair 2164) :=
  singular_series_pos_evenPair (by decide : Even 2164)

theorem singular_series_pos_evenPair_twoThousandOneHundredSixtySix : 0 < singularSeries (evenPair 2166) :=
  singular_series_pos_evenPair (by decide : Even 2166)

theorem singular_series_pos_evenPair_twoThousandOneHundredSixtyEight : 0 < singularSeries (evenPair 2168) :=
  singular_series_pos_evenPair (by decide : Even 2168)

theorem singular_series_pos_evenPair_twoThousandOneHundredSeventy : 0 < singularSeries (evenPair 2170) :=
  singular_series_pos_evenPair (by decide : Even 2170)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2162) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2162) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2164) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2164) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2166) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2166) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2168) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2168) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2170) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2170) P

theorem nu_p_twoThousandOneHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2162) p = if p = 2 ∨ p ∣ 2162 then 1 else 2 :=
  nu_p_evenPair (by decide : (2162 : ℕ) ≠ 0) (by decide : Even 2162) hp

theorem nu_p_twoThousandOneHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2164) p = if p = 2 ∨ p ∣ 2164 then 1 else 2 :=
  nu_p_evenPair (by decide : (2164 : ℕ) ≠ 0) (by decide : Even 2164) hp

theorem nu_p_twoThousandOneHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2166) p = if p = 2 ∨ p ∣ 2166 then 1 else 2 :=
  nu_p_evenPair (by decide : (2166 : ℕ) ≠ 0) (by decide : Even 2166) hp

theorem nu_p_twoThousandOneHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2168) p = if p = 2 ∨ p ∣ 2168 then 1 else 2 :=
  nu_p_evenPair (by decide : (2168 : ℕ) ≠ 0) (by decide : Even 2168) hp

theorem nu_p_twoThousandOneHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2170) p = if p = 2 ∨ p ∣ 2170 then 1 else 2 :=
  nu_p_evenPair (by decide : (2170 : ℕ) ≠ 0) (by decide : Even 2170) hp

theorem nu_p_twoThousandOneHundredSixtyTwo_two : nu_p (evenPair 2162) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2162)

theorem localFactor_twoThousandOneHundredSixtyTwo_two : localFactor (evenPair 2162) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2162 : ℕ) ≠ 0) (by decide : Even 2162)

theorem nu_p_twoThousandOneHundredSeventy_two : nu_p (evenPair 2170) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2170)

theorem localFactor_twoThousandOneHundredSeventy_two : localFactor (evenPair 2170) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2170 : ℕ) ≠ 0) (by decide : Even 2170)

end Brockian.SingularSeries.Gaps21622170
