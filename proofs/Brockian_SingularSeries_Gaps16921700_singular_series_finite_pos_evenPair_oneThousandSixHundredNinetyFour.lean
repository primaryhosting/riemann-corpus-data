/-
  Brockian/SingularSeriesGaps16921700.lean — even binary gaps n ∈ {1692, 1694, 1696, 1698, 1700}.

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

namespace Brockian.SingularSeries.Gaps16921700

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredNinetyTwo : (evenPair 1692).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1692 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredNinetyFour : (evenPair 1694).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1694 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredNinetySix : (evenPair 1696).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1696 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredNinetyEight : (evenPair 1698).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1698 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundred : (evenPair 1700).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1700 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredNinetyTwo : IsAdmissible (evenPair 1692) :=
  isAdmissible_evenPair (by decide : Even 1692)

theorem isAdmissible_evenPair_oneThousandSixHundredNinetyFour : IsAdmissible (evenPair 1694) :=
  isAdmissible_evenPair (by decide : Even 1694)

theorem isAdmissible_evenPair_oneThousandSixHundredNinetySix : IsAdmissible (evenPair 1696) :=
  isAdmissible_evenPair (by decide : Even 1696)

theorem isAdmissible_evenPair_oneThousandSixHundredNinetyEight : IsAdmissible (evenPair 1698) :=
  isAdmissible_evenPair (by decide : Even 1698)

theorem isAdmissible_evenPair_oneThousandSevenHundred : IsAdmissible (evenPair 1700) :=
  isAdmissible_evenPair (by decide : Even 1700)

theorem singular_series_pos_evenPair_oneThousandSixHundredNinetyTwo : 0 < singularSeries (evenPair 1692) :=
  singular_series_pos_evenPair (by decide : Even 1692)

theorem singular_series_pos_evenPair_oneThousandSixHundredNinetyFour : 0 < singularSeries (evenPair 1694) :=
  singular_series_pos_evenPair (by decide : Even 1694)

theorem singular_series_pos_evenPair_oneThousandSixHundredNinetySix : 0 < singularSeries (evenPair 1696) :=
  singular_series_pos_evenPair (by decide : Even 1696)

theorem singular_series_pos_evenPair_oneThousandSixHundredNinetyEight : 0 < singularSeries (evenPair 1698) :=
  singular_series_pos_evenPair (by decide : Even 1698)

theorem singular_series_pos_evenPair_oneThousandSevenHundred : 0 < singularSeries (evenPair 1700) :=
  singular_series_pos_evenPair (by decide : Even 1700)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1692) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1692) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1694) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1694) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1696) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1696) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1698) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1698) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1700) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1700) P

theorem nu_p_oneThousandSixHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1692) p = if p = 2 ∨ p ∣ 1692 then 1 else 2 :=
  nu_p_evenPair (by decide : (1692 : ℕ) ≠ 0) (by decide : Even 1692) hp

theorem nu_p_oneThousandSixHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1694) p = if p = 2 ∨ p ∣ 1694 then 1 else 2 :=
  nu_p_evenPair (by decide : (1694 : ℕ) ≠ 0) (by decide : Even 1694) hp

theorem nu_p_oneThousandSixHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1696) p = if p = 2 ∨ p ∣ 1696 then 1 else 2 :=
  nu_p_evenPair (by decide : (1696 : ℕ) ≠ 0) (by decide : Even 1696) hp

theorem nu_p_oneThousandSixHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1698) p = if p = 2 ∨ p ∣ 1698 then 1 else 2 :=
  nu_p_evenPair (by decide : (1698 : ℕ) ≠ 0) (by decide : Even 1698) hp

theorem nu_p_oneThousandSevenHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1700) p = if p = 2 ∨ p ∣ 1700 then 1 else 2 :=
  nu_p_evenPair (by decide : (1700 : ℕ) ≠ 0) (by decide : Even 1700) hp

theorem nu_p_oneThousandSixHundredNinetyTwo_two : nu_p (evenPair 1692) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1692)

theorem localFactor_oneThousandSixHundredNinetyTwo_two : localFactor (evenPair 1692) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1692 : ℕ) ≠ 0) (by decide : Even 1692)

theorem nu_p_oneThousandSevenHundred_two : nu_p (evenPair 1700) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1700)

theorem localFactor_oneThousandSevenHundred_two : localFactor (evenPair 1700) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1700 : ℕ) ≠ 0) (by decide : Even 1700)

end Brockian.SingularSeries.Gaps16921700
