/-
  Brockian/SingularSeriesGaps20122020.lean — even binary gaps n ∈ {2012, 2014, 2016, 2018, 2020}.

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

namespace Brockian.SingularSeries.Gaps20122020

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandTwelve : (evenPair 2012).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2012 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandFourteen : (evenPair 2014).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2014 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSixteen : (evenPair 2016).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2016 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandEighteen : (evenPair 2018).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2018 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandTwenty : (evenPair 2020).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2020 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandTwelve : IsAdmissible (evenPair 2012) :=
  isAdmissible_evenPair (by decide : Even 2012)

theorem isAdmissible_evenPair_twoThousandFourteen : IsAdmissible (evenPair 2014) :=
  isAdmissible_evenPair (by decide : Even 2014)

theorem isAdmissible_evenPair_twoThousandSixteen : IsAdmissible (evenPair 2016) :=
  isAdmissible_evenPair (by decide : Even 2016)

theorem isAdmissible_evenPair_twoThousandEighteen : IsAdmissible (evenPair 2018) :=
  isAdmissible_evenPair (by decide : Even 2018)

theorem isAdmissible_evenPair_twoThousandTwenty : IsAdmissible (evenPair 2020) :=
  isAdmissible_evenPair (by decide : Even 2020)

theorem singular_series_pos_evenPair_twoThousandTwelve : 0 < singularSeries (evenPair 2012) :=
  singular_series_pos_evenPair (by decide : Even 2012)

theorem singular_series_pos_evenPair_twoThousandFourteen : 0 < singularSeries (evenPair 2014) :=
  singular_series_pos_evenPair (by decide : Even 2014)

theorem singular_series_pos_evenPair_twoThousandSixteen : 0 < singularSeries (evenPair 2016) :=
  singular_series_pos_evenPair (by decide : Even 2016)

theorem singular_series_pos_evenPair_twoThousandEighteen : 0 < singularSeries (evenPair 2018) :=
  singular_series_pos_evenPair (by decide : Even 2018)

theorem singular_series_pos_evenPair_twoThousandTwenty : 0 < singularSeries (evenPair 2020) :=
  singular_series_pos_evenPair (by decide : Even 2020)

theorem singular_series_finite_pos_evenPair_twoThousandTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2012) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2012) P

theorem singular_series_finite_pos_evenPair_twoThousandFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2014) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2014) P

theorem singular_series_finite_pos_evenPair_twoThousandSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2016) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2016) P

theorem singular_series_finite_pos_evenPair_twoThousandEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2018) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2018) P

theorem singular_series_finite_pos_evenPair_twoThousandTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2020) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2020) P

theorem nu_p_twoThousandTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2012) p = if p = 2 ∨ p ∣ 2012 then 1 else 2 :=
  nu_p_evenPair (by decide : (2012 : ℕ) ≠ 0) (by decide : Even 2012) hp

theorem nu_p_twoThousandFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2014) p = if p = 2 ∨ p ∣ 2014 then 1 else 2 :=
  nu_p_evenPair (by decide : (2014 : ℕ) ≠ 0) (by decide : Even 2014) hp

theorem nu_p_twoThousandSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2016) p = if p = 2 ∨ p ∣ 2016 then 1 else 2 :=
  nu_p_evenPair (by decide : (2016 : ℕ) ≠ 0) (by decide : Even 2016) hp

theorem nu_p_twoThousandEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2018) p = if p = 2 ∨ p ∣ 2018 then 1 else 2 :=
  nu_p_evenPair (by decide : (2018 : ℕ) ≠ 0) (by decide : Even 2018) hp

theorem nu_p_twoThousandTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2020) p = if p = 2 ∨ p ∣ 2020 then 1 else 2 :=
  nu_p_evenPair (by decide : (2020 : ℕ) ≠ 0) (by decide : Even 2020) hp

theorem nu_p_twoThousandTwelve_two : nu_p (evenPair 2012) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2012)

theorem localFactor_twoThousandTwelve_two : localFactor (evenPair 2012) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2012 : ℕ) ≠ 0) (by decide : Even 2012)

theorem nu_p_twoThousandTwenty_two : nu_p (evenPair 2020) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2020)

theorem localFactor_twoThousandTwenty_two : localFactor (evenPair 2020) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2020 : ℕ) ≠ 0) (by decide : Even 2020)

end Brockian.SingularSeries.Gaps20122020
