/-
  Brockian/SingularSeriesGaps962970.lean — even binary gaps n ∈ {962, 964, 966, 968, 970}.

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

namespace Brockian.SingularSeries.Gaps962970

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredSixtyTwo : (evenPair 962).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (962 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSixtyFour : (evenPair 964).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (964 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSixtySix : (evenPair 966).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (966 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSixtyEight : (evenPair 968).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (968 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSeventy : (evenPair 970).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (970 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredSixtyTwo : IsAdmissible (evenPair 962) :=
  isAdmissible_evenPair (by decide : Even 962)

theorem isAdmissible_evenPair_nineHundredSixtyFour : IsAdmissible (evenPair 964) :=
  isAdmissible_evenPair (by decide : Even 964)

theorem isAdmissible_evenPair_nineHundredSixtySix : IsAdmissible (evenPair 966) :=
  isAdmissible_evenPair (by decide : Even 966)

theorem isAdmissible_evenPair_nineHundredSixtyEight : IsAdmissible (evenPair 968) :=
  isAdmissible_evenPair (by decide : Even 968)

theorem isAdmissible_evenPair_nineHundredSeventy : IsAdmissible (evenPair 970) :=
  isAdmissible_evenPair (by decide : Even 970)

theorem singular_series_pos_evenPair_nineHundredSixtyTwo : 0 < singularSeries (evenPair 962) :=
  singular_series_pos_evenPair (by decide : Even 962)

theorem singular_series_pos_evenPair_nineHundredSixtyFour : 0 < singularSeries (evenPair 964) :=
  singular_series_pos_evenPair (by decide : Even 964)

theorem singular_series_pos_evenPair_nineHundredSixtySix : 0 < singularSeries (evenPair 966) :=
  singular_series_pos_evenPair (by decide : Even 966)

theorem singular_series_pos_evenPair_nineHundredSixtyEight : 0 < singularSeries (evenPair 968) :=
  singular_series_pos_evenPair (by decide : Even 968)

theorem singular_series_pos_evenPair_nineHundredSeventy : 0 < singularSeries (evenPair 970) :=
  singular_series_pos_evenPair (by decide : Even 970)

theorem singular_series_finite_pos_evenPair_nineHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 962) P :=
  singular_series_finite_pos_evenPair (by decide : Even 962) P

theorem singular_series_finite_pos_evenPair_nineHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 964) P :=
  singular_series_finite_pos_evenPair (by decide : Even 964) P

theorem singular_series_finite_pos_evenPair_nineHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 966) P :=
  singular_series_finite_pos_evenPair (by decide : Even 966) P

theorem singular_series_finite_pos_evenPair_nineHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 968) P :=
  singular_series_finite_pos_evenPair (by decide : Even 968) P

theorem singular_series_finite_pos_evenPair_nineHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 970) P :=
  singular_series_finite_pos_evenPair (by decide : Even 970) P

theorem nu_p_nineHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 962) p = if p = 2 ∨ p ∣ 962 then 1 else 2 :=
  nu_p_evenPair (by decide : (962 : ℕ) ≠ 0) (by decide : Even 962) hp

theorem nu_p_nineHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 964) p = if p = 2 ∨ p ∣ 964 then 1 else 2 :=
  nu_p_evenPair (by decide : (964 : ℕ) ≠ 0) (by decide : Even 964) hp

theorem nu_p_nineHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 966) p = if p = 2 ∨ p ∣ 966 then 1 else 2 :=
  nu_p_evenPair (by decide : (966 : ℕ) ≠ 0) (by decide : Even 966) hp

theorem nu_p_nineHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 968) p = if p = 2 ∨ p ∣ 968 then 1 else 2 :=
  nu_p_evenPair (by decide : (968 : ℕ) ≠ 0) (by decide : Even 968) hp

theorem nu_p_nineHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 970) p = if p = 2 ∨ p ∣ 970 then 1 else 2 :=
  nu_p_evenPair (by decide : (970 : ℕ) ≠ 0) (by decide : Even 970) hp

theorem nu_p_nineHundredSixtyTwo_two : nu_p (evenPair 962) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 962)

theorem localFactor_nineHundredSixtyTwo_two : localFactor (evenPair 962) 2 = 2 :=
  localFactor_evenPair_two (by decide : (962 : ℕ) ≠ 0) (by decide : Even 962)

theorem nu_p_nineHundredSeventy_two : nu_p (evenPair 970) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 970)

theorem localFactor_nineHundredSeventy_two : localFactor (evenPair 970) 2 = 2 :=
  localFactor_evenPair_two (by decide : (970 : ℕ) ≠ 0) (by decide : Even 970)

end Brockian.SingularSeries.Gaps962970
