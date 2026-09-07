/-
  Brockian/SingularSeriesGaps11121120.lean — even binary gaps n ∈ {1112, 1114, 1116, 1118, 1120}.

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

namespace Brockian.SingularSeries.Gaps11121120

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredTwelve : (evenPair 1112).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1112 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredFourteen : (evenPair 1114).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1114 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSixteen : (evenPair 1116).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1116 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredEighteen : (evenPair 1118).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1118 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredTwenty : (evenPair 1120).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1120 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredTwelve : IsAdmissible (evenPair 1112) :=
  isAdmissible_evenPair (by decide : Even 1112)

theorem isAdmissible_evenPair_oneThousandOneHundredFourteen : IsAdmissible (evenPair 1114) :=
  isAdmissible_evenPair (by decide : Even 1114)

theorem isAdmissible_evenPair_oneThousandOneHundredSixteen : IsAdmissible (evenPair 1116) :=
  isAdmissible_evenPair (by decide : Even 1116)

theorem isAdmissible_evenPair_oneThousandOneHundredEighteen : IsAdmissible (evenPair 1118) :=
  isAdmissible_evenPair (by decide : Even 1118)

theorem isAdmissible_evenPair_oneThousandOneHundredTwenty : IsAdmissible (evenPair 1120) :=
  isAdmissible_evenPair (by decide : Even 1120)

theorem singular_series_pos_evenPair_oneThousandOneHundredTwelve : 0 < singularSeries (evenPair 1112) :=
  singular_series_pos_evenPair (by decide : Even 1112)

theorem singular_series_pos_evenPair_oneThousandOneHundredFourteen : 0 < singularSeries (evenPair 1114) :=
  singular_series_pos_evenPair (by decide : Even 1114)

theorem singular_series_pos_evenPair_oneThousandOneHundredSixteen : 0 < singularSeries (evenPair 1116) :=
  singular_series_pos_evenPair (by decide : Even 1116)

theorem singular_series_pos_evenPair_oneThousandOneHundredEighteen : 0 < singularSeries (evenPair 1118) :=
  singular_series_pos_evenPair (by decide : Even 1118)

theorem singular_series_pos_evenPair_oneThousandOneHundredTwenty : 0 < singularSeries (evenPair 1120) :=
  singular_series_pos_evenPair (by decide : Even 1120)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1112) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1112) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1114) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1114) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1116) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1116) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1118) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1118) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1120) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1120) P

theorem nu_p_oneThousandOneHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1112) p = if p = 2 ∨ p ∣ 1112 then 1 else 2 :=
  nu_p_evenPair (by decide : (1112 : ℕ) ≠ 0) (by decide : Even 1112) hp

theorem nu_p_oneThousandOneHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1114) p = if p = 2 ∨ p ∣ 1114 then 1 else 2 :=
  nu_p_evenPair (by decide : (1114 : ℕ) ≠ 0) (by decide : Even 1114) hp

theorem nu_p_oneThousandOneHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1116) p = if p = 2 ∨ p ∣ 1116 then 1 else 2 :=
  nu_p_evenPair (by decide : (1116 : ℕ) ≠ 0) (by decide : Even 1116) hp

theorem nu_p_oneThousandOneHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1118) p = if p = 2 ∨ p ∣ 1118 then 1 else 2 :=
  nu_p_evenPair (by decide : (1118 : ℕ) ≠ 0) (by decide : Even 1118) hp

theorem nu_p_oneThousandOneHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1120) p = if p = 2 ∨ p ∣ 1120 then 1 else 2 :=
  nu_p_evenPair (by decide : (1120 : ℕ) ≠ 0) (by decide : Even 1120) hp

theorem nu_p_oneThousandOneHundredTwelve_two : nu_p (evenPair 1112) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1112)

theorem localFactor_oneThousandOneHundredTwelve_two : localFactor (evenPair 1112) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1112 : ℕ) ≠ 0) (by decide : Even 1112)

theorem nu_p_oneThousandOneHundredTwenty_two : nu_p (evenPair 1120) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1120)

theorem localFactor_oneThousandOneHundredTwenty_two : localFactor (evenPair 1120) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1120 : ℕ) ≠ 0) (by decide : Even 1120)

end Brockian.SingularSeries.Gaps11121120
