/-
  Brockian/SingularSeriesGaps942950.lean — even binary gaps n ∈ {942, 944, 946, 948, 950}.

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

namespace Brockian.SingularSeries.Gaps942950

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredFortyTwo : (evenPair 942).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (942 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredFortyFour : (evenPair 944).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (944 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredFortySix : (evenPair 946).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (946 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredFortyEight : (evenPair 948).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (948 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredFifty : (evenPair 950).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (950 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredFortyTwo : IsAdmissible (evenPair 942) :=
  isAdmissible_evenPair (by decide : Even 942)

theorem isAdmissible_evenPair_nineHundredFortyFour : IsAdmissible (evenPair 944) :=
  isAdmissible_evenPair (by decide : Even 944)

theorem isAdmissible_evenPair_nineHundredFortySix : IsAdmissible (evenPair 946) :=
  isAdmissible_evenPair (by decide : Even 946)

theorem isAdmissible_evenPair_nineHundredFortyEight : IsAdmissible (evenPair 948) :=
  isAdmissible_evenPair (by decide : Even 948)

theorem isAdmissible_evenPair_nineHundredFifty : IsAdmissible (evenPair 950) :=
  isAdmissible_evenPair (by decide : Even 950)

theorem singular_series_pos_evenPair_nineHundredFortyTwo : 0 < singularSeries (evenPair 942) :=
  singular_series_pos_evenPair (by decide : Even 942)

theorem singular_series_pos_evenPair_nineHundredFortyFour : 0 < singularSeries (evenPair 944) :=
  singular_series_pos_evenPair (by decide : Even 944)

theorem singular_series_pos_evenPair_nineHundredFortySix : 0 < singularSeries (evenPair 946) :=
  singular_series_pos_evenPair (by decide : Even 946)

theorem singular_series_pos_evenPair_nineHundredFortyEight : 0 < singularSeries (evenPair 948) :=
  singular_series_pos_evenPair (by decide : Even 948)

theorem singular_series_pos_evenPair_nineHundredFifty : 0 < singularSeries (evenPair 950) :=
  singular_series_pos_evenPair (by decide : Even 950)

theorem singular_series_finite_pos_evenPair_nineHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 942) P :=
  singular_series_finite_pos_evenPair (by decide : Even 942) P

theorem singular_series_finite_pos_evenPair_nineHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 944) P :=
  singular_series_finite_pos_evenPair (by decide : Even 944) P

theorem singular_series_finite_pos_evenPair_nineHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 946) P :=
  singular_series_finite_pos_evenPair (by decide : Even 946) P

theorem singular_series_finite_pos_evenPair_nineHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 948) P :=
  singular_series_finite_pos_evenPair (by decide : Even 948) P

theorem singular_series_finite_pos_evenPair_nineHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 950) P :=
  singular_series_finite_pos_evenPair (by decide : Even 950) P

theorem nu_p_nineHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 942) p = if p = 2 ∨ p ∣ 942 then 1 else 2 :=
  nu_p_evenPair (by decide : (942 : ℕ) ≠ 0) (by decide : Even 942) hp

theorem nu_p_nineHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 944) p = if p = 2 ∨ p ∣ 944 then 1 else 2 :=
  nu_p_evenPair (by decide : (944 : ℕ) ≠ 0) (by decide : Even 944) hp

theorem nu_p_nineHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 946) p = if p = 2 ∨ p ∣ 946 then 1 else 2 :=
  nu_p_evenPair (by decide : (946 : ℕ) ≠ 0) (by decide : Even 946) hp

theorem nu_p_nineHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 948) p = if p = 2 ∨ p ∣ 948 then 1 else 2 :=
  nu_p_evenPair (by decide : (948 : ℕ) ≠ 0) (by decide : Even 948) hp

theorem nu_p_nineHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 950) p = if p = 2 ∨ p ∣ 950 then 1 else 2 :=
  nu_p_evenPair (by decide : (950 : ℕ) ≠ 0) (by decide : Even 950) hp

theorem nu_p_nineHundredFortyTwo_two : nu_p (evenPair 942) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 942)

theorem localFactor_nineHundredFortyTwo_two : localFactor (evenPair 942) 2 = 2 :=
  localFactor_evenPair_two (by decide : (942 : ℕ) ≠ 0) (by decide : Even 942)

theorem nu_p_nineHundredFifty_two : nu_p (evenPair 950) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 950)

theorem localFactor_nineHundredFifty_two : localFactor (evenPair 950) 2 = 2 :=
  localFactor_evenPair_two (by decide : (950 : ℕ) ≠ 0) (by decide : Even 950)

end Brockian.SingularSeries.Gaps942950
