/-
  Brockian/SingularSeriesGaps112120.lean — even binary gaps n ∈ {112, 114, 116, 118, 120}.

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

namespace Brockian.SingularSeries.Gaps112120

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
theorem evenPair_card_oneHundredTwelve : (evenPair 112).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (112 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredFourteen : (evenPair 114).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (114 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSixteen : (evenPair 116).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (116 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredEighteen : (evenPair 118).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (118 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredTwenty : (evenPair 120).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (120 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredTwelve : IsAdmissible (evenPair 112) :=
  isAdmissible_evenPair (by decide : Even 112)

theorem isAdmissible_evenPair_oneHundredFourteen : IsAdmissible (evenPair 114) :=
  isAdmissible_evenPair (by decide : Even 114)

theorem isAdmissible_evenPair_oneHundredSixteen : IsAdmissible (evenPair 116) :=
  isAdmissible_evenPair (by decide : Even 116)

theorem isAdmissible_evenPair_oneHundredEighteen : IsAdmissible (evenPair 118) :=
  isAdmissible_evenPair (by decide : Even 118)

theorem isAdmissible_evenPair_oneHundredTwenty : IsAdmissible (evenPair 120) :=
  isAdmissible_evenPair (by decide : Even 120)

theorem singular_series_pos_evenPair_oneHundredTwelve : 0 < singularSeries (evenPair 112) :=
  singular_series_pos_evenPair (by decide : Even 112)

theorem singular_series_pos_evenPair_oneHundredFourteen : 0 < singularSeries (evenPair 114) :=
  singular_series_pos_evenPair (by decide : Even 114)

theorem singular_series_pos_evenPair_oneHundredSixteen : 0 < singularSeries (evenPair 116) :=
  singular_series_pos_evenPair (by decide : Even 116)

theorem singular_series_pos_evenPair_oneHundredEighteen : 0 < singularSeries (evenPair 118) :=
  singular_series_pos_evenPair (by decide : Even 118)

theorem singular_series_pos_evenPair_oneHundredTwenty : 0 < singularSeries (evenPair 120) :=
  singular_series_pos_evenPair (by decide : Even 120)

theorem singular_series_finite_pos_evenPair_oneHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 112) P :=
  singular_series_finite_pos_evenPair (by decide : Even 112) P

theorem singular_series_finite_pos_evenPair_oneHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 114) P :=
  singular_series_finite_pos_evenPair (by decide : Even 114) P

theorem singular_series_finite_pos_evenPair_oneHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 116) P :=
  singular_series_finite_pos_evenPair (by decide : Even 116) P

theorem singular_series_finite_pos_evenPair_oneHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 118) P :=
  singular_series_finite_pos_evenPair (by decide : Even 118) P

theorem singular_series_finite_pos_evenPair_oneHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 120) P :=
  singular_series_finite_pos_evenPair (by decide : Even 120) P

theorem nu_p_oneHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 112) p = if p = 2 ∨ p ∣ 112 then 1 else 2 :=
  nu_p_evenPair (by decide : (112 : ℕ) ≠ 0) (by decide : Even 112) hp

theorem nu_p_oneHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 114) p = if p = 2 ∨ p ∣ 114 then 1 else 2 :=
  nu_p_evenPair (by decide : (114 : ℕ) ≠ 0) (by decide : Even 114) hp

theorem nu_p_oneHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 116) p = if p = 2 ∨ p ∣ 116 then 1 else 2 :=
  nu_p_evenPair (by decide : (116 : ℕ) ≠ 0) (by decide : Even 116) hp

theorem nu_p_oneHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 118) p = if p = 2 ∨ p ∣ 118 then 1 else 2 :=
  nu_p_evenPair (by decide : (118 : ℕ) ≠ 0) (by decide : Even 118) hp

theorem nu_p_oneHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 120) p = if p = 2 ∨ p ∣ 120 then 1 else 2 :=
  nu_p_evenPair (by decide : (120 : ℕ) ≠ 0) (by decide : Even 120) hp

theorem nu_p_oneHundredTwelve_two : nu_p (evenPair 112) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 112)

theorem localFactor_oneHundredTwelve_two : localFactor (evenPair 112) 2 = 2 :=
  localFactor_evenPair_two (by decide : (112 : ℕ) ≠ 0) (by decide : Even 112)

theorem nu_p_oneHundredTwenty_two : nu_p (evenPair 120) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 120)

theorem localFactor_oneHundredTwenty_two : localFactor (evenPair 120) 2 = 2 :=
  localFactor_evenPair_two (by decide : (120 : ℕ) ≠ 0) (by decide : Even 120)

end Brockian.SingularSeries.Gaps112120
