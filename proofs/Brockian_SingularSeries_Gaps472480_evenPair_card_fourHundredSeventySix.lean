/-
  Brockian/SingularSeriesGaps472480.lean — even binary gaps n ∈ {472, 474, 476, 478, 480}.

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

namespace Brockian.SingularSeries.Gaps472480

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredSeventyTwo : (evenPair 472).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (472 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSeventyFour : (evenPair 474).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (474 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSeventySix : (evenPair 476).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (476 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSeventyEight : (evenPair 478).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (478 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredEighty : (evenPair 480).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (480 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredSeventyTwo : IsAdmissible (evenPair 472) :=
  isAdmissible_evenPair (by decide : Even 472)

theorem isAdmissible_evenPair_fourHundredSeventyFour : IsAdmissible (evenPair 474) :=
  isAdmissible_evenPair (by decide : Even 474)

theorem isAdmissible_evenPair_fourHundredSeventySix : IsAdmissible (evenPair 476) :=
  isAdmissible_evenPair (by decide : Even 476)

theorem isAdmissible_evenPair_fourHundredSeventyEight : IsAdmissible (evenPair 478) :=
  isAdmissible_evenPair (by decide : Even 478)

theorem isAdmissible_evenPair_fourHundredEighty : IsAdmissible (evenPair 480) :=
  isAdmissible_evenPair (by decide : Even 480)

theorem singular_series_pos_evenPair_fourHundredSeventyTwo : 0 < singularSeries (evenPair 472) :=
  singular_series_pos_evenPair (by decide : Even 472)

theorem singular_series_pos_evenPair_fourHundredSeventyFour : 0 < singularSeries (evenPair 474) :=
  singular_series_pos_evenPair (by decide : Even 474)

theorem singular_series_pos_evenPair_fourHundredSeventySix : 0 < singularSeries (evenPair 476) :=
  singular_series_pos_evenPair (by decide : Even 476)

theorem singular_series_pos_evenPair_fourHundredSeventyEight : 0 < singularSeries (evenPair 478) :=
  singular_series_pos_evenPair (by decide : Even 478)

theorem singular_series_pos_evenPair_fourHundredEighty : 0 < singularSeries (evenPair 480) :=
  singular_series_pos_evenPair (by decide : Even 480)

theorem singular_series_finite_pos_evenPair_fourHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 472) P :=
  singular_series_finite_pos_evenPair (by decide : Even 472) P

theorem singular_series_finite_pos_evenPair_fourHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 474) P :=
  singular_series_finite_pos_evenPair (by decide : Even 474) P

theorem singular_series_finite_pos_evenPair_fourHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 476) P :=
  singular_series_finite_pos_evenPair (by decide : Even 476) P

theorem singular_series_finite_pos_evenPair_fourHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 478) P :=
  singular_series_finite_pos_evenPair (by decide : Even 478) P

theorem singular_series_finite_pos_evenPair_fourHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 480) P :=
  singular_series_finite_pos_evenPair (by decide : Even 480) P

theorem nu_p_fourHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 472) p = if p = 2 ∨ p ∣ 472 then 1 else 2 :=
  nu_p_evenPair (by decide : (472 : ℕ) ≠ 0) (by decide : Even 472) hp

theorem nu_p_fourHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 474) p = if p = 2 ∨ p ∣ 474 then 1 else 2 :=
  nu_p_evenPair (by decide : (474 : ℕ) ≠ 0) (by decide : Even 474) hp

theorem nu_p_fourHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 476) p = if p = 2 ∨ p ∣ 476 then 1 else 2 :=
  nu_p_evenPair (by decide : (476 : ℕ) ≠ 0) (by decide : Even 476) hp

theorem nu_p_fourHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 478) p = if p = 2 ∨ p ∣ 478 then 1 else 2 :=
  nu_p_evenPair (by decide : (478 : ℕ) ≠ 0) (by decide : Even 478) hp

theorem nu_p_fourHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 480) p = if p = 2 ∨ p ∣ 480 then 1 else 2 :=
  nu_p_evenPair (by decide : (480 : ℕ) ≠ 0) (by decide : Even 480) hp

theorem nu_p_fourHundredSeventyTwo_two : nu_p (evenPair 472) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 472)

theorem localFactor_fourHundredSeventyTwo_two : localFactor (evenPair 472) 2 = 2 :=
  localFactor_evenPair_two (by decide : (472 : ℕ) ≠ 0) (by decide : Even 472)

theorem nu_p_fourHundredEighty_two : nu_p (evenPair 480) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 480)

theorem localFactor_fourHundredEighty_two : localFactor (evenPair 480) 2 = 2 :=
  localFactor_evenPair_two (by decide : (480 : ℕ) ≠ 0) (by decide : Even 480)

end Brockian.SingularSeries.Gaps472480
