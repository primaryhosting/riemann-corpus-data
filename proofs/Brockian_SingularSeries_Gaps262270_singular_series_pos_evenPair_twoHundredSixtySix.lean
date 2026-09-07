/-
  Brockian/SingularSeriesGaps262270.lean — even binary gaps n ∈ {262, 264, 266, 268, 270}.

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

namespace Brockian.SingularSeries.Gaps262270

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredSixtyTwo : (evenPair 262).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (262 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSixtyFour : (evenPair 264).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (264 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSixtySix : (evenPair 266).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (266 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSixtyEight : (evenPair 268).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (268 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSeventy : (evenPair 270).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (270 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredSixtyTwo : IsAdmissible (evenPair 262) :=
  isAdmissible_evenPair (by decide : Even 262)

theorem isAdmissible_evenPair_twoHundredSixtyFour : IsAdmissible (evenPair 264) :=
  isAdmissible_evenPair (by decide : Even 264)

theorem isAdmissible_evenPair_twoHundredSixtySix : IsAdmissible (evenPair 266) :=
  isAdmissible_evenPair (by decide : Even 266)

theorem isAdmissible_evenPair_twoHundredSixtyEight : IsAdmissible (evenPair 268) :=
  isAdmissible_evenPair (by decide : Even 268)

theorem isAdmissible_evenPair_twoHundredSeventy : IsAdmissible (evenPair 270) :=
  isAdmissible_evenPair (by decide : Even 270)

theorem singular_series_pos_evenPair_twoHundredSixtyTwo : 0 < singularSeries (evenPair 262) :=
  singular_series_pos_evenPair (by decide : Even 262)

theorem singular_series_pos_evenPair_twoHundredSixtyFour : 0 < singularSeries (evenPair 264) :=
  singular_series_pos_evenPair (by decide : Even 264)

theorem singular_series_pos_evenPair_twoHundredSixtySix : 0 < singularSeries (evenPair 266) :=
  singular_series_pos_evenPair (by decide : Even 266)

theorem singular_series_pos_evenPair_twoHundredSixtyEight : 0 < singularSeries (evenPair 268) :=
  singular_series_pos_evenPair (by decide : Even 268)

theorem singular_series_pos_evenPair_twoHundredSeventy : 0 < singularSeries (evenPair 270) :=
  singular_series_pos_evenPair (by decide : Even 270)

theorem singular_series_finite_pos_evenPair_twoHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 262) P :=
  singular_series_finite_pos_evenPair (by decide : Even 262) P

theorem singular_series_finite_pos_evenPair_twoHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 264) P :=
  singular_series_finite_pos_evenPair (by decide : Even 264) P

theorem singular_series_finite_pos_evenPair_twoHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 266) P :=
  singular_series_finite_pos_evenPair (by decide : Even 266) P

theorem singular_series_finite_pos_evenPair_twoHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 268) P :=
  singular_series_finite_pos_evenPair (by decide : Even 268) P

theorem singular_series_finite_pos_evenPair_twoHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 270) P :=
  singular_series_finite_pos_evenPair (by decide : Even 270) P

theorem nu_p_twoHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 262) p = if p = 2 ∨ p ∣ 262 then 1 else 2 :=
  nu_p_evenPair (by decide : (262 : ℕ) ≠ 0) (by decide : Even 262) hp

theorem nu_p_twoHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 264) p = if p = 2 ∨ p ∣ 264 then 1 else 2 :=
  nu_p_evenPair (by decide : (264 : ℕ) ≠ 0) (by decide : Even 264) hp

theorem nu_p_twoHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 266) p = if p = 2 ∨ p ∣ 266 then 1 else 2 :=
  nu_p_evenPair (by decide : (266 : ℕ) ≠ 0) (by decide : Even 266) hp

theorem nu_p_twoHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 268) p = if p = 2 ∨ p ∣ 268 then 1 else 2 :=
  nu_p_evenPair (by decide : (268 : ℕ) ≠ 0) (by decide : Even 268) hp

theorem nu_p_twoHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 270) p = if p = 2 ∨ p ∣ 270 then 1 else 2 :=
  nu_p_evenPair (by decide : (270 : ℕ) ≠ 0) (by decide : Even 270) hp

theorem nu_p_twoHundredSixtyTwo_two : nu_p (evenPair 262) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 262)

theorem localFactor_twoHundredSixtyTwo_two : localFactor (evenPair 262) 2 = 2 :=
  localFactor_evenPair_two (by decide : (262 : ℕ) ≠ 0) (by decide : Even 262)

theorem nu_p_twoHundredSeventy_two : nu_p (evenPair 270) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 270)

theorem localFactor_twoHundredSeventy_two : localFactor (evenPair 270) 2 = 2 :=
  localFactor_evenPair_two (by decide : (270 : ℕ) ≠ 0) (by decide : Even 270)

end Brockian.SingularSeries.Gaps262270
