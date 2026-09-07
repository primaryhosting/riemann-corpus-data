/-
  Brockian/SingularSeriesGaps862870.lean — even binary gaps n ∈ {862, 864, 866, 868, 870}.

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

namespace Brockian.SingularSeries.Gaps862870

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredSixtyTwo : (evenPair 862).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (862 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSixtyFour : (evenPair 864).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (864 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSixtySix : (evenPair 866).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (866 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSixtyEight : (evenPair 868).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (868 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSeventy : (evenPair 870).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (870 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredSixtyTwo : IsAdmissible (evenPair 862) :=
  isAdmissible_evenPair (by decide : Even 862)

theorem isAdmissible_evenPair_eightHundredSixtyFour : IsAdmissible (evenPair 864) :=
  isAdmissible_evenPair (by decide : Even 864)

theorem isAdmissible_evenPair_eightHundredSixtySix : IsAdmissible (evenPair 866) :=
  isAdmissible_evenPair (by decide : Even 866)

theorem isAdmissible_evenPair_eightHundredSixtyEight : IsAdmissible (evenPair 868) :=
  isAdmissible_evenPair (by decide : Even 868)

theorem isAdmissible_evenPair_eightHundredSeventy : IsAdmissible (evenPair 870) :=
  isAdmissible_evenPair (by decide : Even 870)

theorem singular_series_pos_evenPair_eightHundredSixtyTwo : 0 < singularSeries (evenPair 862) :=
  singular_series_pos_evenPair (by decide : Even 862)

theorem singular_series_pos_evenPair_eightHundredSixtyFour : 0 < singularSeries (evenPair 864) :=
  singular_series_pos_evenPair (by decide : Even 864)

theorem singular_series_pos_evenPair_eightHundredSixtySix : 0 < singularSeries (evenPair 866) :=
  singular_series_pos_evenPair (by decide : Even 866)

theorem singular_series_pos_evenPair_eightHundredSixtyEight : 0 < singularSeries (evenPair 868) :=
  singular_series_pos_evenPair (by decide : Even 868)

theorem singular_series_pos_evenPair_eightHundredSeventy : 0 < singularSeries (evenPair 870) :=
  singular_series_pos_evenPair (by decide : Even 870)

theorem singular_series_finite_pos_evenPair_eightHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 862) P :=
  singular_series_finite_pos_evenPair (by decide : Even 862) P

theorem singular_series_finite_pos_evenPair_eightHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 864) P :=
  singular_series_finite_pos_evenPair (by decide : Even 864) P

theorem singular_series_finite_pos_evenPair_eightHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 866) P :=
  singular_series_finite_pos_evenPair (by decide : Even 866) P

theorem singular_series_finite_pos_evenPair_eightHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 868) P :=
  singular_series_finite_pos_evenPair (by decide : Even 868) P

theorem singular_series_finite_pos_evenPair_eightHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 870) P :=
  singular_series_finite_pos_evenPair (by decide : Even 870) P

theorem nu_p_eightHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 862) p = if p = 2 ∨ p ∣ 862 then 1 else 2 :=
  nu_p_evenPair (by decide : (862 : ℕ) ≠ 0) (by decide : Even 862) hp

theorem nu_p_eightHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 864) p = if p = 2 ∨ p ∣ 864 then 1 else 2 :=
  nu_p_evenPair (by decide : (864 : ℕ) ≠ 0) (by decide : Even 864) hp

theorem nu_p_eightHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 866) p = if p = 2 ∨ p ∣ 866 then 1 else 2 :=
  nu_p_evenPair (by decide : (866 : ℕ) ≠ 0) (by decide : Even 866) hp

theorem nu_p_eightHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 868) p = if p = 2 ∨ p ∣ 868 then 1 else 2 :=
  nu_p_evenPair (by decide : (868 : ℕ) ≠ 0) (by decide : Even 868) hp

theorem nu_p_eightHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 870) p = if p = 2 ∨ p ∣ 870 then 1 else 2 :=
  nu_p_evenPair (by decide : (870 : ℕ) ≠ 0) (by decide : Even 870) hp

theorem nu_p_eightHundredSixtyTwo_two : nu_p (evenPair 862) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 862)

theorem localFactor_eightHundredSixtyTwo_two : localFactor (evenPair 862) 2 = 2 :=
  localFactor_evenPair_two (by decide : (862 : ℕ) ≠ 0) (by decide : Even 862)

theorem nu_p_eightHundredSeventy_two : nu_p (evenPair 870) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 870)

theorem localFactor_eightHundredSeventy_two : localFactor (evenPair 870) 2 = 2 :=
  localFactor_evenPair_two (by decide : (870 : ℕ) ≠ 0) (by decide : Even 870)

end Brockian.SingularSeries.Gaps862870
