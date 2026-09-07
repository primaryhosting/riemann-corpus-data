/-
  Brockian/SingularSeriesGaps232240.lean — even binary gaps n ∈ {232, 234, 236, 238, 240}.

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

namespace Brockian.SingularSeries.Gaps232240

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredThirtyTwo : (evenPair 232).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (232 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredThirtyFour : (evenPair 234).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (234 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredThirtySix : (evenPair 236).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (236 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredThirtyEight : (evenPair 238).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (238 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredForty : (evenPair 240).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (240 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredThirtyTwo : IsAdmissible (evenPair 232) :=
  isAdmissible_evenPair (by decide : Even 232)

theorem isAdmissible_evenPair_twoHundredThirtyFour : IsAdmissible (evenPair 234) :=
  isAdmissible_evenPair (by decide : Even 234)

theorem isAdmissible_evenPair_twoHundredThirtySix : IsAdmissible (evenPair 236) :=
  isAdmissible_evenPair (by decide : Even 236)

theorem isAdmissible_evenPair_twoHundredThirtyEight : IsAdmissible (evenPair 238) :=
  isAdmissible_evenPair (by decide : Even 238)

theorem isAdmissible_evenPair_twoHundredForty : IsAdmissible (evenPair 240) :=
  isAdmissible_evenPair (by decide : Even 240)

theorem singular_series_pos_evenPair_twoHundredThirtyTwo : 0 < singularSeries (evenPair 232) :=
  singular_series_pos_evenPair (by decide : Even 232)

theorem singular_series_pos_evenPair_twoHundredThirtyFour : 0 < singularSeries (evenPair 234) :=
  singular_series_pos_evenPair (by decide : Even 234)

theorem singular_series_pos_evenPair_twoHundredThirtySix : 0 < singularSeries (evenPair 236) :=
  singular_series_pos_evenPair (by decide : Even 236)

theorem singular_series_pos_evenPair_twoHundredThirtyEight : 0 < singularSeries (evenPair 238) :=
  singular_series_pos_evenPair (by decide : Even 238)

theorem singular_series_pos_evenPair_twoHundredForty : 0 < singularSeries (evenPair 240) :=
  singular_series_pos_evenPair (by decide : Even 240)

theorem singular_series_finite_pos_evenPair_twoHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 232) P :=
  singular_series_finite_pos_evenPair (by decide : Even 232) P

theorem singular_series_finite_pos_evenPair_twoHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 234) P :=
  singular_series_finite_pos_evenPair (by decide : Even 234) P

theorem singular_series_finite_pos_evenPair_twoHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 236) P :=
  singular_series_finite_pos_evenPair (by decide : Even 236) P

theorem singular_series_finite_pos_evenPair_twoHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 238) P :=
  singular_series_finite_pos_evenPair (by decide : Even 238) P

theorem singular_series_finite_pos_evenPair_twoHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 240) P :=
  singular_series_finite_pos_evenPair (by decide : Even 240) P

theorem nu_p_twoHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 232) p = if p = 2 ∨ p ∣ 232 then 1 else 2 :=
  nu_p_evenPair (by decide : (232 : ℕ) ≠ 0) (by decide : Even 232) hp

theorem nu_p_twoHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 234) p = if p = 2 ∨ p ∣ 234 then 1 else 2 :=
  nu_p_evenPair (by decide : (234 : ℕ) ≠ 0) (by decide : Even 234) hp

theorem nu_p_twoHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 236) p = if p = 2 ∨ p ∣ 236 then 1 else 2 :=
  nu_p_evenPair (by decide : (236 : ℕ) ≠ 0) (by decide : Even 236) hp

theorem nu_p_twoHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 238) p = if p = 2 ∨ p ∣ 238 then 1 else 2 :=
  nu_p_evenPair (by decide : (238 : ℕ) ≠ 0) (by decide : Even 238) hp

theorem nu_p_twoHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 240) p = if p = 2 ∨ p ∣ 240 then 1 else 2 :=
  nu_p_evenPair (by decide : (240 : ℕ) ≠ 0) (by decide : Even 240) hp

theorem nu_p_twoHundredThirtyTwo_two : nu_p (evenPair 232) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 232)

theorem localFactor_twoHundredThirtyTwo_two : localFactor (evenPair 232) 2 = 2 :=
  localFactor_evenPair_two (by decide : (232 : ℕ) ≠ 0) (by decide : Even 232)

theorem nu_p_twoHundredForty_two : nu_p (evenPair 240) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 240)

theorem localFactor_twoHundredForty_two : localFactor (evenPair 240) 2 = 2 :=
  localFactor_evenPair_two (by decide : (240 : ℕ) ≠ 0) (by decide : Even 240)

end Brockian.SingularSeries.Gaps232240
