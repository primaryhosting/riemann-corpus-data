/-
  Brockian/SingularSeriesGaps812820.lean — even binary gaps n ∈ {812, 814, 816, 818, 820}.

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

namespace Brockian.SingularSeries.Gaps812820

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredTwelve : (evenPair 812).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (812 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredFourteen : (evenPair 814).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (814 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSixteen : (evenPair 816).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (816 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredEighteen : (evenPair 818).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (818 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredTwenty : (evenPair 820).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (820 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredTwelve : IsAdmissible (evenPair 812) :=
  isAdmissible_evenPair (by decide : Even 812)

theorem isAdmissible_evenPair_eightHundredFourteen : IsAdmissible (evenPair 814) :=
  isAdmissible_evenPair (by decide : Even 814)

theorem isAdmissible_evenPair_eightHundredSixteen : IsAdmissible (evenPair 816) :=
  isAdmissible_evenPair (by decide : Even 816)

theorem isAdmissible_evenPair_eightHundredEighteen : IsAdmissible (evenPair 818) :=
  isAdmissible_evenPair (by decide : Even 818)

theorem isAdmissible_evenPair_eightHundredTwenty : IsAdmissible (evenPair 820) :=
  isAdmissible_evenPair (by decide : Even 820)

theorem singular_series_pos_evenPair_eightHundredTwelve : 0 < singularSeries (evenPair 812) :=
  singular_series_pos_evenPair (by decide : Even 812)

theorem singular_series_pos_evenPair_eightHundredFourteen : 0 < singularSeries (evenPair 814) :=
  singular_series_pos_evenPair (by decide : Even 814)

theorem singular_series_pos_evenPair_eightHundredSixteen : 0 < singularSeries (evenPair 816) :=
  singular_series_pos_evenPair (by decide : Even 816)

theorem singular_series_pos_evenPair_eightHundredEighteen : 0 < singularSeries (evenPair 818) :=
  singular_series_pos_evenPair (by decide : Even 818)

theorem singular_series_pos_evenPair_eightHundredTwenty : 0 < singularSeries (evenPair 820) :=
  singular_series_pos_evenPair (by decide : Even 820)

theorem singular_series_finite_pos_evenPair_eightHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 812) P :=
  singular_series_finite_pos_evenPair (by decide : Even 812) P

theorem singular_series_finite_pos_evenPair_eightHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 814) P :=
  singular_series_finite_pos_evenPair (by decide : Even 814) P

theorem singular_series_finite_pos_evenPair_eightHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 816) P :=
  singular_series_finite_pos_evenPair (by decide : Even 816) P

theorem singular_series_finite_pos_evenPair_eightHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 818) P :=
  singular_series_finite_pos_evenPair (by decide : Even 818) P

theorem singular_series_finite_pos_evenPair_eightHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 820) P :=
  singular_series_finite_pos_evenPair (by decide : Even 820) P

theorem nu_p_eightHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 812) p = if p = 2 ∨ p ∣ 812 then 1 else 2 :=
  nu_p_evenPair (by decide : (812 : ℕ) ≠ 0) (by decide : Even 812) hp

theorem nu_p_eightHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 814) p = if p = 2 ∨ p ∣ 814 then 1 else 2 :=
  nu_p_evenPair (by decide : (814 : ℕ) ≠ 0) (by decide : Even 814) hp

theorem nu_p_eightHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 816) p = if p = 2 ∨ p ∣ 816 then 1 else 2 :=
  nu_p_evenPair (by decide : (816 : ℕ) ≠ 0) (by decide : Even 816) hp

theorem nu_p_eightHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 818) p = if p = 2 ∨ p ∣ 818 then 1 else 2 :=
  nu_p_evenPair (by decide : (818 : ℕ) ≠ 0) (by decide : Even 818) hp

theorem nu_p_eightHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 820) p = if p = 2 ∨ p ∣ 820 then 1 else 2 :=
  nu_p_evenPair (by decide : (820 : ℕ) ≠ 0) (by decide : Even 820) hp

theorem nu_p_eightHundredTwelve_two : nu_p (evenPair 812) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 812)

theorem localFactor_eightHundredTwelve_two : localFactor (evenPair 812) 2 = 2 :=
  localFactor_evenPair_two (by decide : (812 : ℕ) ≠ 0) (by decide : Even 812)

theorem nu_p_eightHundredTwenty_two : nu_p (evenPair 820) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 820)

theorem localFactor_eightHundredTwenty_two : localFactor (evenPair 820) 2 = 2 :=
  localFactor_evenPair_two (by decide : (820 : ℕ) ≠ 0) (by decide : Even 820)

end Brockian.SingularSeries.Gaps812820
