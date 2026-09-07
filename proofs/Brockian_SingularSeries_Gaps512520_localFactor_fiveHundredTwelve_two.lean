/-
  Brockian/SingularSeriesGaps512520.lean — even binary gaps n ∈ {512, 514, 516, 518, 520}.

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

namespace Brockian.SingularSeries.Gaps512520

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredTwelve : (evenPair 512).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (512 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredFourteen : (evenPair 514).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (514 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSixteen : (evenPair 516).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (516 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredEighteen : (evenPair 518).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (518 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredTwenty : (evenPair 520).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (520 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredTwelve : IsAdmissible (evenPair 512) :=
  isAdmissible_evenPair (by decide : Even 512)

theorem isAdmissible_evenPair_fiveHundredFourteen : IsAdmissible (evenPair 514) :=
  isAdmissible_evenPair (by decide : Even 514)

theorem isAdmissible_evenPair_fiveHundredSixteen : IsAdmissible (evenPair 516) :=
  isAdmissible_evenPair (by decide : Even 516)

theorem isAdmissible_evenPair_fiveHundredEighteen : IsAdmissible (evenPair 518) :=
  isAdmissible_evenPair (by decide : Even 518)

theorem isAdmissible_evenPair_fiveHundredTwenty : IsAdmissible (evenPair 520) :=
  isAdmissible_evenPair (by decide : Even 520)

theorem singular_series_pos_evenPair_fiveHundredTwelve : 0 < singularSeries (evenPair 512) :=
  singular_series_pos_evenPair (by decide : Even 512)

theorem singular_series_pos_evenPair_fiveHundredFourteen : 0 < singularSeries (evenPair 514) :=
  singular_series_pos_evenPair (by decide : Even 514)

theorem singular_series_pos_evenPair_fiveHundredSixteen : 0 < singularSeries (evenPair 516) :=
  singular_series_pos_evenPair (by decide : Even 516)

theorem singular_series_pos_evenPair_fiveHundredEighteen : 0 < singularSeries (evenPair 518) :=
  singular_series_pos_evenPair (by decide : Even 518)

theorem singular_series_pos_evenPair_fiveHundredTwenty : 0 < singularSeries (evenPair 520) :=
  singular_series_pos_evenPair (by decide : Even 520)

theorem singular_series_finite_pos_evenPair_fiveHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 512) P :=
  singular_series_finite_pos_evenPair (by decide : Even 512) P

theorem singular_series_finite_pos_evenPair_fiveHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 514) P :=
  singular_series_finite_pos_evenPair (by decide : Even 514) P

theorem singular_series_finite_pos_evenPair_fiveHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 516) P :=
  singular_series_finite_pos_evenPair (by decide : Even 516) P

theorem singular_series_finite_pos_evenPair_fiveHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 518) P :=
  singular_series_finite_pos_evenPair (by decide : Even 518) P

theorem singular_series_finite_pos_evenPair_fiveHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 520) P :=
  singular_series_finite_pos_evenPair (by decide : Even 520) P

theorem nu_p_fiveHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 512) p = if p = 2 ∨ p ∣ 512 then 1 else 2 :=
  nu_p_evenPair (by decide : (512 : ℕ) ≠ 0) (by decide : Even 512) hp

theorem nu_p_fiveHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 514) p = if p = 2 ∨ p ∣ 514 then 1 else 2 :=
  nu_p_evenPair (by decide : (514 : ℕ) ≠ 0) (by decide : Even 514) hp

theorem nu_p_fiveHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 516) p = if p = 2 ∨ p ∣ 516 then 1 else 2 :=
  nu_p_evenPair (by decide : (516 : ℕ) ≠ 0) (by decide : Even 516) hp

theorem nu_p_fiveHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 518) p = if p = 2 ∨ p ∣ 518 then 1 else 2 :=
  nu_p_evenPair (by decide : (518 : ℕ) ≠ 0) (by decide : Even 518) hp

theorem nu_p_fiveHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 520) p = if p = 2 ∨ p ∣ 520 then 1 else 2 :=
  nu_p_evenPair (by decide : (520 : ℕ) ≠ 0) (by decide : Even 520) hp

theorem nu_p_fiveHundredTwelve_two : nu_p (evenPair 512) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 512)

theorem localFactor_fiveHundredTwelve_two : localFactor (evenPair 512) 2 = 2 :=
  localFactor_evenPair_two (by decide : (512 : ℕ) ≠ 0) (by decide : Even 512)

theorem nu_p_fiveHundredTwenty_two : nu_p (evenPair 520) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 520)

theorem localFactor_fiveHundredTwenty_two : localFactor (evenPair 520) 2 = 2 :=
  localFactor_evenPair_two (by decide : (520 : ℕ) ≠ 0) (by decide : Even 520)

end Brockian.SingularSeries.Gaps512520
