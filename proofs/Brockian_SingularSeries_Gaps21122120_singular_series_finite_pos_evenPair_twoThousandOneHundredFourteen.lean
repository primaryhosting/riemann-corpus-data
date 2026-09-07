/-
  Brockian/SingularSeriesGaps21122120.lean — even binary gaps n ∈ {2112, 2114, 2116, 2118, 2120}.

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

namespace Brockian.SingularSeries.Gaps21122120

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredTwelve : (evenPair 2112).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2112 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredFourteen : (evenPair 2114).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2114 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSixteen : (evenPair 2116).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2116 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredEighteen : (evenPair 2118).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2118 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredTwenty : (evenPair 2120).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2120 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredTwelve : IsAdmissible (evenPair 2112) :=
  isAdmissible_evenPair (by decide : Even 2112)

theorem isAdmissible_evenPair_twoThousandOneHundredFourteen : IsAdmissible (evenPair 2114) :=
  isAdmissible_evenPair (by decide : Even 2114)

theorem isAdmissible_evenPair_twoThousandOneHundredSixteen : IsAdmissible (evenPair 2116) :=
  isAdmissible_evenPair (by decide : Even 2116)

theorem isAdmissible_evenPair_twoThousandOneHundredEighteen : IsAdmissible (evenPair 2118) :=
  isAdmissible_evenPair (by decide : Even 2118)

theorem isAdmissible_evenPair_twoThousandOneHundredTwenty : IsAdmissible (evenPair 2120) :=
  isAdmissible_evenPair (by decide : Even 2120)

theorem singular_series_pos_evenPair_twoThousandOneHundredTwelve : 0 < singularSeries (evenPair 2112) :=
  singular_series_pos_evenPair (by decide : Even 2112)

theorem singular_series_pos_evenPair_twoThousandOneHundredFourteen : 0 < singularSeries (evenPair 2114) :=
  singular_series_pos_evenPair (by decide : Even 2114)

theorem singular_series_pos_evenPair_twoThousandOneHundredSixteen : 0 < singularSeries (evenPair 2116) :=
  singular_series_pos_evenPair (by decide : Even 2116)

theorem singular_series_pos_evenPair_twoThousandOneHundredEighteen : 0 < singularSeries (evenPair 2118) :=
  singular_series_pos_evenPair (by decide : Even 2118)

theorem singular_series_pos_evenPair_twoThousandOneHundredTwenty : 0 < singularSeries (evenPair 2120) :=
  singular_series_pos_evenPair (by decide : Even 2120)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2112) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2112) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2114) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2114) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2116) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2116) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2118) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2118) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2120) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2120) P

theorem nu_p_twoThousandOneHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2112) p = if p = 2 ∨ p ∣ 2112 then 1 else 2 :=
  nu_p_evenPair (by decide : (2112 : ℕ) ≠ 0) (by decide : Even 2112) hp

theorem nu_p_twoThousandOneHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2114) p = if p = 2 ∨ p ∣ 2114 then 1 else 2 :=
  nu_p_evenPair (by decide : (2114 : ℕ) ≠ 0) (by decide : Even 2114) hp

theorem nu_p_twoThousandOneHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2116) p = if p = 2 ∨ p ∣ 2116 then 1 else 2 :=
  nu_p_evenPair (by decide : (2116 : ℕ) ≠ 0) (by decide : Even 2116) hp

theorem nu_p_twoThousandOneHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2118) p = if p = 2 ∨ p ∣ 2118 then 1 else 2 :=
  nu_p_evenPair (by decide : (2118 : ℕ) ≠ 0) (by decide : Even 2118) hp

theorem nu_p_twoThousandOneHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2120) p = if p = 2 ∨ p ∣ 2120 then 1 else 2 :=
  nu_p_evenPair (by decide : (2120 : ℕ) ≠ 0) (by decide : Even 2120) hp

theorem nu_p_twoThousandOneHundredTwelve_two : nu_p (evenPair 2112) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2112)

theorem localFactor_twoThousandOneHundredTwelve_two : localFactor (evenPair 2112) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2112 : ℕ) ≠ 0) (by decide : Even 2112)

theorem nu_p_twoThousandOneHundredTwenty_two : nu_p (evenPair 2120) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2120)

theorem localFactor_twoThousandOneHundredTwenty_two : localFactor (evenPair 2120) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2120 : ℕ) ≠ 0) (by decide : Even 2120)

end Brockian.SingularSeries.Gaps21122120
