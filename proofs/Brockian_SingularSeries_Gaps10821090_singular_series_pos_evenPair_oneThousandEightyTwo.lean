/-
  Brockian/SingularSeriesGaps10821090.lean — even binary gaps n ∈ {1082, 1084, 1086, 1088, 1090}.

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

namespace Brockian.SingularSeries.Gaps10821090

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightyTwo : (evenPair 1082).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1082 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightyFour : (evenPair 1084).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1084 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightySix : (evenPair 1086).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1086 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightyEight : (evenPair 1088).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1088 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNinety : (evenPair 1090).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1090 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightyTwo : IsAdmissible (evenPair 1082) :=
  isAdmissible_evenPair (by decide : Even 1082)

theorem isAdmissible_evenPair_oneThousandEightyFour : IsAdmissible (evenPair 1084) :=
  isAdmissible_evenPair (by decide : Even 1084)

theorem isAdmissible_evenPair_oneThousandEightySix : IsAdmissible (evenPair 1086) :=
  isAdmissible_evenPair (by decide : Even 1086)

theorem isAdmissible_evenPair_oneThousandEightyEight : IsAdmissible (evenPair 1088) :=
  isAdmissible_evenPair (by decide : Even 1088)

theorem isAdmissible_evenPair_oneThousandNinety : IsAdmissible (evenPair 1090) :=
  isAdmissible_evenPair (by decide : Even 1090)

theorem singular_series_pos_evenPair_oneThousandEightyTwo : 0 < singularSeries (evenPair 1082) :=
  singular_series_pos_evenPair (by decide : Even 1082)

theorem singular_series_pos_evenPair_oneThousandEightyFour : 0 < singularSeries (evenPair 1084) :=
  singular_series_pos_evenPair (by decide : Even 1084)

theorem singular_series_pos_evenPair_oneThousandEightySix : 0 < singularSeries (evenPair 1086) :=
  singular_series_pos_evenPair (by decide : Even 1086)

theorem singular_series_pos_evenPair_oneThousandEightyEight : 0 < singularSeries (evenPair 1088) :=
  singular_series_pos_evenPair (by decide : Even 1088)

theorem singular_series_pos_evenPair_oneThousandNinety : 0 < singularSeries (evenPair 1090) :=
  singular_series_pos_evenPair (by decide : Even 1090)

theorem singular_series_finite_pos_evenPair_oneThousandEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1082) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1082) P

theorem singular_series_finite_pos_evenPair_oneThousandEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1084) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1084) P

theorem singular_series_finite_pos_evenPair_oneThousandEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1086) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1086) P

theorem singular_series_finite_pos_evenPair_oneThousandEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1088) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1088) P

theorem singular_series_finite_pos_evenPair_oneThousandNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1090) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1090) P

theorem nu_p_oneThousandEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1082) p = if p = 2 ∨ p ∣ 1082 then 1 else 2 :=
  nu_p_evenPair (by decide : (1082 : ℕ) ≠ 0) (by decide : Even 1082) hp

theorem nu_p_oneThousandEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1084) p = if p = 2 ∨ p ∣ 1084 then 1 else 2 :=
  nu_p_evenPair (by decide : (1084 : ℕ) ≠ 0) (by decide : Even 1084) hp

theorem nu_p_oneThousandEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1086) p = if p = 2 ∨ p ∣ 1086 then 1 else 2 :=
  nu_p_evenPair (by decide : (1086 : ℕ) ≠ 0) (by decide : Even 1086) hp

theorem nu_p_oneThousandEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1088) p = if p = 2 ∨ p ∣ 1088 then 1 else 2 :=
  nu_p_evenPair (by decide : (1088 : ℕ) ≠ 0) (by decide : Even 1088) hp

theorem nu_p_oneThousandNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1090) p = if p = 2 ∨ p ∣ 1090 then 1 else 2 :=
  nu_p_evenPair (by decide : (1090 : ℕ) ≠ 0) (by decide : Even 1090) hp

theorem nu_p_oneThousandEightyTwo_two : nu_p (evenPair 1082) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1082)

theorem localFactor_oneThousandEightyTwo_two : localFactor (evenPair 1082) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1082 : ℕ) ≠ 0) (by decide : Even 1082)

theorem nu_p_oneThousandNinety_two : nu_p (evenPair 1090) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1090)

theorem localFactor_oneThousandNinety_two : localFactor (evenPair 1090) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1090 : ℕ) ≠ 0) (by decide : Even 1090)

end Brockian.SingularSeries.Gaps10821090
