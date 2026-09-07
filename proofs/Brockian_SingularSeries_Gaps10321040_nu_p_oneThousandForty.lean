/-
  Brockian/SingularSeriesGaps10321040.lean — even binary gaps n ∈ {1032, 1034, 1036, 1038, 1040}.

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

namespace Brockian.SingularSeries.Gaps10321040

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThirtyTwo : (evenPair 1032).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1032 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThirtyFour : (evenPair 1034).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1034 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThirtySix : (evenPair 1036).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1036 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThirtyEight : (evenPair 1038).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1038 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandForty : (evenPair 1040).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1040 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThirtyTwo : IsAdmissible (evenPair 1032) :=
  isAdmissible_evenPair (by decide : Even 1032)

theorem isAdmissible_evenPair_oneThousandThirtyFour : IsAdmissible (evenPair 1034) :=
  isAdmissible_evenPair (by decide : Even 1034)

theorem isAdmissible_evenPair_oneThousandThirtySix : IsAdmissible (evenPair 1036) :=
  isAdmissible_evenPair (by decide : Even 1036)

theorem isAdmissible_evenPair_oneThousandThirtyEight : IsAdmissible (evenPair 1038) :=
  isAdmissible_evenPair (by decide : Even 1038)

theorem isAdmissible_evenPair_oneThousandForty : IsAdmissible (evenPair 1040) :=
  isAdmissible_evenPair (by decide : Even 1040)

theorem singular_series_pos_evenPair_oneThousandThirtyTwo : 0 < singularSeries (evenPair 1032) :=
  singular_series_pos_evenPair (by decide : Even 1032)

theorem singular_series_pos_evenPair_oneThousandThirtyFour : 0 < singularSeries (evenPair 1034) :=
  singular_series_pos_evenPair (by decide : Even 1034)

theorem singular_series_pos_evenPair_oneThousandThirtySix : 0 < singularSeries (evenPair 1036) :=
  singular_series_pos_evenPair (by decide : Even 1036)

theorem singular_series_pos_evenPair_oneThousandThirtyEight : 0 < singularSeries (evenPair 1038) :=
  singular_series_pos_evenPair (by decide : Even 1038)

theorem singular_series_pos_evenPair_oneThousandForty : 0 < singularSeries (evenPair 1040) :=
  singular_series_pos_evenPair (by decide : Even 1040)

theorem singular_series_finite_pos_evenPair_oneThousandThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1032) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1032) P

theorem singular_series_finite_pos_evenPair_oneThousandThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1034) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1034) P

theorem singular_series_finite_pos_evenPair_oneThousandThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1036) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1036) P

theorem singular_series_finite_pos_evenPair_oneThousandThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1038) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1038) P

theorem singular_series_finite_pos_evenPair_oneThousandForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1040) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1040) P

theorem nu_p_oneThousandThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1032) p = if p = 2 ∨ p ∣ 1032 then 1 else 2 :=
  nu_p_evenPair (by decide : (1032 : ℕ) ≠ 0) (by decide : Even 1032) hp

theorem nu_p_oneThousandThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1034) p = if p = 2 ∨ p ∣ 1034 then 1 else 2 :=
  nu_p_evenPair (by decide : (1034 : ℕ) ≠ 0) (by decide : Even 1034) hp

theorem nu_p_oneThousandThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1036) p = if p = 2 ∨ p ∣ 1036 then 1 else 2 :=
  nu_p_evenPair (by decide : (1036 : ℕ) ≠ 0) (by decide : Even 1036) hp

theorem nu_p_oneThousandThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1038) p = if p = 2 ∨ p ∣ 1038 then 1 else 2 :=
  nu_p_evenPair (by decide : (1038 : ℕ) ≠ 0) (by decide : Even 1038) hp

theorem nu_p_oneThousandForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1040) p = if p = 2 ∨ p ∣ 1040 then 1 else 2 :=
  nu_p_evenPair (by decide : (1040 : ℕ) ≠ 0) (by decide : Even 1040) hp

theorem nu_p_oneThousandThirtyTwo_two : nu_p (evenPair 1032) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1032)

theorem localFactor_oneThousandThirtyTwo_two : localFactor (evenPair 1032) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1032 : ℕ) ≠ 0) (by decide : Even 1032)

theorem nu_p_oneThousandForty_two : nu_p (evenPair 1040) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1040)

theorem localFactor_oneThousandForty_two : localFactor (evenPair 1040) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1040 : ℕ) ≠ 0) (by decide : Even 1040)

end Brockian.SingularSeries.Gaps10321040
