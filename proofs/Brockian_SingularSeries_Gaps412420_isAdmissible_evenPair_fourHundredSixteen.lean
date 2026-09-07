/-
  Brockian/SingularSeriesGaps412420.lean — even binary gaps n ∈ {412, 414, 416, 418, 420}.

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

namespace Brockian.SingularSeries.Gaps412420

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredTwelve : (evenPair 412).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (412 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredFourteen : (evenPair 414).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (414 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSixteen : (evenPair 416).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (416 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredEighteen : (evenPair 418).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (418 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredTwenty : (evenPair 420).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (420 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredTwelve : IsAdmissible (evenPair 412) :=
  isAdmissible_evenPair (by decide : Even 412)

theorem isAdmissible_evenPair_fourHundredFourteen : IsAdmissible (evenPair 414) :=
  isAdmissible_evenPair (by decide : Even 414)

theorem isAdmissible_evenPair_fourHundredSixteen : IsAdmissible (evenPair 416) :=
  isAdmissible_evenPair (by decide : Even 416)

theorem isAdmissible_evenPair_fourHundredEighteen : IsAdmissible (evenPair 418) :=
  isAdmissible_evenPair (by decide : Even 418)

theorem isAdmissible_evenPair_fourHundredTwenty : IsAdmissible (evenPair 420) :=
  isAdmissible_evenPair (by decide : Even 420)

theorem singular_series_pos_evenPair_fourHundredTwelve : 0 < singularSeries (evenPair 412) :=
  singular_series_pos_evenPair (by decide : Even 412)

theorem singular_series_pos_evenPair_fourHundredFourteen : 0 < singularSeries (evenPair 414) :=
  singular_series_pos_evenPair (by decide : Even 414)

theorem singular_series_pos_evenPair_fourHundredSixteen : 0 < singularSeries (evenPair 416) :=
  singular_series_pos_evenPair (by decide : Even 416)

theorem singular_series_pos_evenPair_fourHundredEighteen : 0 < singularSeries (evenPair 418) :=
  singular_series_pos_evenPair (by decide : Even 418)

theorem singular_series_pos_evenPair_fourHundredTwenty : 0 < singularSeries (evenPair 420) :=
  singular_series_pos_evenPair (by decide : Even 420)

theorem singular_series_finite_pos_evenPair_fourHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 412) P :=
  singular_series_finite_pos_evenPair (by decide : Even 412) P

theorem singular_series_finite_pos_evenPair_fourHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 414) P :=
  singular_series_finite_pos_evenPair (by decide : Even 414) P

theorem singular_series_finite_pos_evenPair_fourHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 416) P :=
  singular_series_finite_pos_evenPair (by decide : Even 416) P

theorem singular_series_finite_pos_evenPair_fourHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 418) P :=
  singular_series_finite_pos_evenPair (by decide : Even 418) P

theorem singular_series_finite_pos_evenPair_fourHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 420) P :=
  singular_series_finite_pos_evenPair (by decide : Even 420) P

theorem nu_p_fourHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 412) p = if p = 2 ∨ p ∣ 412 then 1 else 2 :=
  nu_p_evenPair (by decide : (412 : ℕ) ≠ 0) (by decide : Even 412) hp

theorem nu_p_fourHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 414) p = if p = 2 ∨ p ∣ 414 then 1 else 2 :=
  nu_p_evenPair (by decide : (414 : ℕ) ≠ 0) (by decide : Even 414) hp

theorem nu_p_fourHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 416) p = if p = 2 ∨ p ∣ 416 then 1 else 2 :=
  nu_p_evenPair (by decide : (416 : ℕ) ≠ 0) (by decide : Even 416) hp

theorem nu_p_fourHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 418) p = if p = 2 ∨ p ∣ 418 then 1 else 2 :=
  nu_p_evenPair (by decide : (418 : ℕ) ≠ 0) (by decide : Even 418) hp

theorem nu_p_fourHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 420) p = if p = 2 ∨ p ∣ 420 then 1 else 2 :=
  nu_p_evenPair (by decide : (420 : ℕ) ≠ 0) (by decide : Even 420) hp

theorem nu_p_fourHundredTwelve_two : nu_p (evenPair 412) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 412)

theorem localFactor_fourHundredTwelve_two : localFactor (evenPair 412) 2 = 2 :=
  localFactor_evenPair_two (by decide : (412 : ℕ) ≠ 0) (by decide : Even 412)

theorem nu_p_fourHundredTwenty_two : nu_p (evenPair 420) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 420)

theorem localFactor_fourHundredTwenty_two : localFactor (evenPair 420) 2 = 2 :=
  localFactor_evenPair_two (by decide : (420 : ℕ) ≠ 0) (by decide : Even 420)

end Brockian.SingularSeries.Gaps412420
