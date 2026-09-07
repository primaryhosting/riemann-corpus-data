/-
  Brockian/SingularSeriesGaps10121020.lean — even binary gaps n ∈ {1012, 1014, 1016, 1018, 1020}.

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

namespace Brockian.SingularSeries.Gaps10121020

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwelve : (evenPair 1012).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1012 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourteen : (evenPair 1014).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1014 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixteen : (evenPair 1016).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1016 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEighteen : (evenPair 1018).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1018 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwenty : (evenPair 1020).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1020 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwelve : IsAdmissible (evenPair 1012) :=
  isAdmissible_evenPair (by decide : Even 1012)

theorem isAdmissible_evenPair_oneThousandFourteen : IsAdmissible (evenPair 1014) :=
  isAdmissible_evenPair (by decide : Even 1014)

theorem isAdmissible_evenPair_oneThousandSixteen : IsAdmissible (evenPair 1016) :=
  isAdmissible_evenPair (by decide : Even 1016)

theorem isAdmissible_evenPair_oneThousandEighteen : IsAdmissible (evenPair 1018) :=
  isAdmissible_evenPair (by decide : Even 1018)

theorem isAdmissible_evenPair_oneThousandTwenty : IsAdmissible (evenPair 1020) :=
  isAdmissible_evenPair (by decide : Even 1020)

theorem singular_series_pos_evenPair_oneThousandTwelve : 0 < singularSeries (evenPair 1012) :=
  singular_series_pos_evenPair (by decide : Even 1012)

theorem singular_series_pos_evenPair_oneThousandFourteen : 0 < singularSeries (evenPair 1014) :=
  singular_series_pos_evenPair (by decide : Even 1014)

theorem singular_series_pos_evenPair_oneThousandSixteen : 0 < singularSeries (evenPair 1016) :=
  singular_series_pos_evenPair (by decide : Even 1016)

theorem singular_series_pos_evenPair_oneThousandEighteen : 0 < singularSeries (evenPair 1018) :=
  singular_series_pos_evenPair (by decide : Even 1018)

theorem singular_series_pos_evenPair_oneThousandTwenty : 0 < singularSeries (evenPair 1020) :=
  singular_series_pos_evenPair (by decide : Even 1020)

theorem singular_series_finite_pos_evenPair_oneThousandTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1012) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1012) P

theorem singular_series_finite_pos_evenPair_oneThousandFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1014) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1014) P

theorem singular_series_finite_pos_evenPair_oneThousandSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1016) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1016) P

theorem singular_series_finite_pos_evenPair_oneThousandEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1018) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1018) P

theorem singular_series_finite_pos_evenPair_oneThousandTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1020) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1020) P

theorem nu_p_oneThousandTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1012) p = if p = 2 ∨ p ∣ 1012 then 1 else 2 :=
  nu_p_evenPair (by decide : (1012 : ℕ) ≠ 0) (by decide : Even 1012) hp

theorem nu_p_oneThousandFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1014) p = if p = 2 ∨ p ∣ 1014 then 1 else 2 :=
  nu_p_evenPair (by decide : (1014 : ℕ) ≠ 0) (by decide : Even 1014) hp

theorem nu_p_oneThousandSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1016) p = if p = 2 ∨ p ∣ 1016 then 1 else 2 :=
  nu_p_evenPair (by decide : (1016 : ℕ) ≠ 0) (by decide : Even 1016) hp

theorem nu_p_oneThousandEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1018) p = if p = 2 ∨ p ∣ 1018 then 1 else 2 :=
  nu_p_evenPair (by decide : (1018 : ℕ) ≠ 0) (by decide : Even 1018) hp

theorem nu_p_oneThousandTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1020) p = if p = 2 ∨ p ∣ 1020 then 1 else 2 :=
  nu_p_evenPair (by decide : (1020 : ℕ) ≠ 0) (by decide : Even 1020) hp

theorem nu_p_oneThousandTwelve_two : nu_p (evenPair 1012) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1012)

theorem localFactor_oneThousandTwelve_two : localFactor (evenPair 1012) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1012 : ℕ) ≠ 0) (by decide : Even 1012)

theorem nu_p_oneThousandTwenty_two : nu_p (evenPair 1020) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1020)

theorem localFactor_oneThousandTwenty_two : localFactor (evenPair 1020) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1020 : ℕ) ≠ 0) (by decide : Even 1020)

end Brockian.SingularSeries.Gaps10121020
