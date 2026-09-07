/-
  Brockian/SingularSeriesGaps672680.lean — even binary gaps n ∈ {672, 674, 676, 678, 680}.

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

namespace Brockian.SingularSeries.Gaps672680

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredSeventyTwo : (evenPair 672).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (672 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSeventyFour : (evenPair 674).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (674 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSeventySix : (evenPair 676).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (676 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSeventyEight : (evenPair 678).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (678 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredEighty : (evenPair 680).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (680 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredSeventyTwo : IsAdmissible (evenPair 672) :=
  isAdmissible_evenPair (by decide : Even 672)

theorem isAdmissible_evenPair_sixHundredSeventyFour : IsAdmissible (evenPair 674) :=
  isAdmissible_evenPair (by decide : Even 674)

theorem isAdmissible_evenPair_sixHundredSeventySix : IsAdmissible (evenPair 676) :=
  isAdmissible_evenPair (by decide : Even 676)

theorem isAdmissible_evenPair_sixHundredSeventyEight : IsAdmissible (evenPair 678) :=
  isAdmissible_evenPair (by decide : Even 678)

theorem isAdmissible_evenPair_sixHundredEighty : IsAdmissible (evenPair 680) :=
  isAdmissible_evenPair (by decide : Even 680)

theorem singular_series_pos_evenPair_sixHundredSeventyTwo : 0 < singularSeries (evenPair 672) :=
  singular_series_pos_evenPair (by decide : Even 672)

theorem singular_series_pos_evenPair_sixHundredSeventyFour : 0 < singularSeries (evenPair 674) :=
  singular_series_pos_evenPair (by decide : Even 674)

theorem singular_series_pos_evenPair_sixHundredSeventySix : 0 < singularSeries (evenPair 676) :=
  singular_series_pos_evenPair (by decide : Even 676)

theorem singular_series_pos_evenPair_sixHundredSeventyEight : 0 < singularSeries (evenPair 678) :=
  singular_series_pos_evenPair (by decide : Even 678)

theorem singular_series_pos_evenPair_sixHundredEighty : 0 < singularSeries (evenPair 680) :=
  singular_series_pos_evenPair (by decide : Even 680)

theorem singular_series_finite_pos_evenPair_sixHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 672) P :=
  singular_series_finite_pos_evenPair (by decide : Even 672) P

theorem singular_series_finite_pos_evenPair_sixHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 674) P :=
  singular_series_finite_pos_evenPair (by decide : Even 674) P

theorem singular_series_finite_pos_evenPair_sixHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 676) P :=
  singular_series_finite_pos_evenPair (by decide : Even 676) P

theorem singular_series_finite_pos_evenPair_sixHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 678) P :=
  singular_series_finite_pos_evenPair (by decide : Even 678) P

theorem singular_series_finite_pos_evenPair_sixHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 680) P :=
  singular_series_finite_pos_evenPair (by decide : Even 680) P

theorem nu_p_sixHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 672) p = if p = 2 ∨ p ∣ 672 then 1 else 2 :=
  nu_p_evenPair (by decide : (672 : ℕ) ≠ 0) (by decide : Even 672) hp

theorem nu_p_sixHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 674) p = if p = 2 ∨ p ∣ 674 then 1 else 2 :=
  nu_p_evenPair (by decide : (674 : ℕ) ≠ 0) (by decide : Even 674) hp

theorem nu_p_sixHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 676) p = if p = 2 ∨ p ∣ 676 then 1 else 2 :=
  nu_p_evenPair (by decide : (676 : ℕ) ≠ 0) (by decide : Even 676) hp

theorem nu_p_sixHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 678) p = if p = 2 ∨ p ∣ 678 then 1 else 2 :=
  nu_p_evenPair (by decide : (678 : ℕ) ≠ 0) (by decide : Even 678) hp

theorem nu_p_sixHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 680) p = if p = 2 ∨ p ∣ 680 then 1 else 2 :=
  nu_p_evenPair (by decide : (680 : ℕ) ≠ 0) (by decide : Even 680) hp

theorem nu_p_sixHundredSeventyTwo_two : nu_p (evenPair 672) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 672)

theorem localFactor_sixHundredSeventyTwo_two : localFactor (evenPair 672) 2 = 2 :=
  localFactor_evenPair_two (by decide : (672 : ℕ) ≠ 0) (by decide : Even 672)

theorem nu_p_sixHundredEighty_two : nu_p (evenPair 680) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 680)

theorem localFactor_sixHundredEighty_two : localFactor (evenPair 680) 2 = 2 :=
  localFactor_evenPair_two (by decide : (680 : ℕ) ≠ 0) (by decide : Even 680)

end Brockian.SingularSeries.Gaps672680
