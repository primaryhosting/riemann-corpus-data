/-
  Brockian/SingularSeriesGaps11621170.lean — even binary gaps n ∈ {1162, 1164, 1166, 1168, 1170}.

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

namespace Brockian.SingularSeries.Gaps11621170

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredSixtyTwo : (evenPair 1162).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1162 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSixtyFour : (evenPair 1164).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1164 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSixtySix : (evenPair 1166).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1166 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSixtyEight : (evenPair 1168).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1168 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSeventy : (evenPair 1170).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1170 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredSixtyTwo : IsAdmissible (evenPair 1162) :=
  isAdmissible_evenPair (by decide : Even 1162)

theorem isAdmissible_evenPair_oneThousandOneHundredSixtyFour : IsAdmissible (evenPair 1164) :=
  isAdmissible_evenPair (by decide : Even 1164)

theorem isAdmissible_evenPair_oneThousandOneHundredSixtySix : IsAdmissible (evenPair 1166) :=
  isAdmissible_evenPair (by decide : Even 1166)

theorem isAdmissible_evenPair_oneThousandOneHundredSixtyEight : IsAdmissible (evenPair 1168) :=
  isAdmissible_evenPair (by decide : Even 1168)

theorem isAdmissible_evenPair_oneThousandOneHundredSeventy : IsAdmissible (evenPair 1170) :=
  isAdmissible_evenPair (by decide : Even 1170)

theorem singular_series_pos_evenPair_oneThousandOneHundredSixtyTwo : 0 < singularSeries (evenPair 1162) :=
  singular_series_pos_evenPair (by decide : Even 1162)

theorem singular_series_pos_evenPair_oneThousandOneHundredSixtyFour : 0 < singularSeries (evenPair 1164) :=
  singular_series_pos_evenPair (by decide : Even 1164)

theorem singular_series_pos_evenPair_oneThousandOneHundredSixtySix : 0 < singularSeries (evenPair 1166) :=
  singular_series_pos_evenPair (by decide : Even 1166)

theorem singular_series_pos_evenPair_oneThousandOneHundredSixtyEight : 0 < singularSeries (evenPair 1168) :=
  singular_series_pos_evenPair (by decide : Even 1168)

theorem singular_series_pos_evenPair_oneThousandOneHundredSeventy : 0 < singularSeries (evenPair 1170) :=
  singular_series_pos_evenPair (by decide : Even 1170)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1162) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1162) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1164) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1164) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1166) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1166) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1168) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1168) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1170) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1170) P

theorem nu_p_oneThousandOneHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1162) p = if p = 2 ∨ p ∣ 1162 then 1 else 2 :=
  nu_p_evenPair (by decide : (1162 : ℕ) ≠ 0) (by decide : Even 1162) hp

theorem nu_p_oneThousandOneHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1164) p = if p = 2 ∨ p ∣ 1164 then 1 else 2 :=
  nu_p_evenPair (by decide : (1164 : ℕ) ≠ 0) (by decide : Even 1164) hp

theorem nu_p_oneThousandOneHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1166) p = if p = 2 ∨ p ∣ 1166 then 1 else 2 :=
  nu_p_evenPair (by decide : (1166 : ℕ) ≠ 0) (by decide : Even 1166) hp

theorem nu_p_oneThousandOneHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1168) p = if p = 2 ∨ p ∣ 1168 then 1 else 2 :=
  nu_p_evenPair (by decide : (1168 : ℕ) ≠ 0) (by decide : Even 1168) hp

theorem nu_p_oneThousandOneHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1170) p = if p = 2 ∨ p ∣ 1170 then 1 else 2 :=
  nu_p_evenPair (by decide : (1170 : ℕ) ≠ 0) (by decide : Even 1170) hp

theorem nu_p_oneThousandOneHundredSixtyTwo_two : nu_p (evenPair 1162) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1162)

theorem localFactor_oneThousandOneHundredSixtyTwo_two : localFactor (evenPair 1162) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1162 : ℕ) ≠ 0) (by decide : Even 1162)

theorem nu_p_oneThousandOneHundredSeventy_two : nu_p (evenPair 1170) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1170)

theorem localFactor_oneThousandOneHundredSeventy_two : localFactor (evenPair 1170) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1170 : ℕ) ≠ 0) (by decide : Even 1170)

end Brockian.SingularSeries.Gaps11621170
