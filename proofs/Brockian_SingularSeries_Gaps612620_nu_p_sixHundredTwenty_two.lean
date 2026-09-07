/-
  Brockian/SingularSeriesGaps612620.lean — even binary gaps n ∈ {612, 614, 616, 618, 620}.

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

namespace Brockian.SingularSeries.Gaps612620

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredTwelve : (evenPair 612).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (612 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredFourteen : (evenPair 614).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (614 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSixteen : (evenPair 616).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (616 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredEighteen : (evenPair 618).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (618 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredTwenty : (evenPair 620).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (620 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredTwelve : IsAdmissible (evenPair 612) :=
  isAdmissible_evenPair (by decide : Even 612)

theorem isAdmissible_evenPair_sixHundredFourteen : IsAdmissible (evenPair 614) :=
  isAdmissible_evenPair (by decide : Even 614)

theorem isAdmissible_evenPair_sixHundredSixteen : IsAdmissible (evenPair 616) :=
  isAdmissible_evenPair (by decide : Even 616)

theorem isAdmissible_evenPair_sixHundredEighteen : IsAdmissible (evenPair 618) :=
  isAdmissible_evenPair (by decide : Even 618)

theorem isAdmissible_evenPair_sixHundredTwenty : IsAdmissible (evenPair 620) :=
  isAdmissible_evenPair (by decide : Even 620)

theorem singular_series_pos_evenPair_sixHundredTwelve : 0 < singularSeries (evenPair 612) :=
  singular_series_pos_evenPair (by decide : Even 612)

theorem singular_series_pos_evenPair_sixHundredFourteen : 0 < singularSeries (evenPair 614) :=
  singular_series_pos_evenPair (by decide : Even 614)

theorem singular_series_pos_evenPair_sixHundredSixteen : 0 < singularSeries (evenPair 616) :=
  singular_series_pos_evenPair (by decide : Even 616)

theorem singular_series_pos_evenPair_sixHundredEighteen : 0 < singularSeries (evenPair 618) :=
  singular_series_pos_evenPair (by decide : Even 618)

theorem singular_series_pos_evenPair_sixHundredTwenty : 0 < singularSeries (evenPair 620) :=
  singular_series_pos_evenPair (by decide : Even 620)

theorem singular_series_finite_pos_evenPair_sixHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 612) P :=
  singular_series_finite_pos_evenPair (by decide : Even 612) P

theorem singular_series_finite_pos_evenPair_sixHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 614) P :=
  singular_series_finite_pos_evenPair (by decide : Even 614) P

theorem singular_series_finite_pos_evenPair_sixHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 616) P :=
  singular_series_finite_pos_evenPair (by decide : Even 616) P

theorem singular_series_finite_pos_evenPair_sixHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 618) P :=
  singular_series_finite_pos_evenPair (by decide : Even 618) P

theorem singular_series_finite_pos_evenPair_sixHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 620) P :=
  singular_series_finite_pos_evenPair (by decide : Even 620) P

theorem nu_p_sixHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 612) p = if p = 2 ∨ p ∣ 612 then 1 else 2 :=
  nu_p_evenPair (by decide : (612 : ℕ) ≠ 0) (by decide : Even 612) hp

theorem nu_p_sixHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 614) p = if p = 2 ∨ p ∣ 614 then 1 else 2 :=
  nu_p_evenPair (by decide : (614 : ℕ) ≠ 0) (by decide : Even 614) hp

theorem nu_p_sixHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 616) p = if p = 2 ∨ p ∣ 616 then 1 else 2 :=
  nu_p_evenPair (by decide : (616 : ℕ) ≠ 0) (by decide : Even 616) hp

theorem nu_p_sixHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 618) p = if p = 2 ∨ p ∣ 618 then 1 else 2 :=
  nu_p_evenPair (by decide : (618 : ℕ) ≠ 0) (by decide : Even 618) hp

theorem nu_p_sixHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 620) p = if p = 2 ∨ p ∣ 620 then 1 else 2 :=
  nu_p_evenPair (by decide : (620 : ℕ) ≠ 0) (by decide : Even 620) hp

theorem nu_p_sixHundredTwelve_two : nu_p (evenPair 612) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 612)

theorem localFactor_sixHundredTwelve_two : localFactor (evenPair 612) 2 = 2 :=
  localFactor_evenPair_two (by decide : (612 : ℕ) ≠ 0) (by decide : Even 612)

theorem nu_p_sixHundredTwenty_two : nu_p (evenPair 620) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 620)

theorem localFactor_sixHundredTwenty_two : localFactor (evenPair 620) 2 = 2 :=
  localFactor_evenPair_two (by decide : (620 : ℕ) ≠ 0) (by decide : Even 620)

end Brockian.SingularSeries.Gaps612620
