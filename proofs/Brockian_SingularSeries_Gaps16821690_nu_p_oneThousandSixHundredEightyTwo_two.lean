/-
  Brockian/SingularSeriesGaps16821690.lean — even binary gaps n ∈ {1682, 1684, 1686, 1688, 1690}.

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

namespace Brockian.SingularSeries.Gaps16821690

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredEightyTwo : (evenPair 1682).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1682 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredEightyFour : (evenPair 1684).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1684 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredEightySix : (evenPair 1686).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1686 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredEightyEight : (evenPair 1688).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1688 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredNinety : (evenPair 1690).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1690 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredEightyTwo : IsAdmissible (evenPair 1682) :=
  isAdmissible_evenPair (by decide : Even 1682)

theorem isAdmissible_evenPair_oneThousandSixHundredEightyFour : IsAdmissible (evenPair 1684) :=
  isAdmissible_evenPair (by decide : Even 1684)

theorem isAdmissible_evenPair_oneThousandSixHundredEightySix : IsAdmissible (evenPair 1686) :=
  isAdmissible_evenPair (by decide : Even 1686)

theorem isAdmissible_evenPair_oneThousandSixHundredEightyEight : IsAdmissible (evenPair 1688) :=
  isAdmissible_evenPair (by decide : Even 1688)

theorem isAdmissible_evenPair_oneThousandSixHundredNinety : IsAdmissible (evenPair 1690) :=
  isAdmissible_evenPair (by decide : Even 1690)

theorem singular_series_pos_evenPair_oneThousandSixHundredEightyTwo : 0 < singularSeries (evenPair 1682) :=
  singular_series_pos_evenPair (by decide : Even 1682)

theorem singular_series_pos_evenPair_oneThousandSixHundredEightyFour : 0 < singularSeries (evenPair 1684) :=
  singular_series_pos_evenPair (by decide : Even 1684)

theorem singular_series_pos_evenPair_oneThousandSixHundredEightySix : 0 < singularSeries (evenPair 1686) :=
  singular_series_pos_evenPair (by decide : Even 1686)

theorem singular_series_pos_evenPair_oneThousandSixHundredEightyEight : 0 < singularSeries (evenPair 1688) :=
  singular_series_pos_evenPair (by decide : Even 1688)

theorem singular_series_pos_evenPair_oneThousandSixHundredNinety : 0 < singularSeries (evenPair 1690) :=
  singular_series_pos_evenPair (by decide : Even 1690)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1682) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1682) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1684) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1684) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1686) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1686) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1688) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1688) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1690) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1690) P

theorem nu_p_oneThousandSixHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1682) p = if p = 2 ∨ p ∣ 1682 then 1 else 2 :=
  nu_p_evenPair (by decide : (1682 : ℕ) ≠ 0) (by decide : Even 1682) hp

theorem nu_p_oneThousandSixHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1684) p = if p = 2 ∨ p ∣ 1684 then 1 else 2 :=
  nu_p_evenPair (by decide : (1684 : ℕ) ≠ 0) (by decide : Even 1684) hp

theorem nu_p_oneThousandSixHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1686) p = if p = 2 ∨ p ∣ 1686 then 1 else 2 :=
  nu_p_evenPair (by decide : (1686 : ℕ) ≠ 0) (by decide : Even 1686) hp

theorem nu_p_oneThousandSixHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1688) p = if p = 2 ∨ p ∣ 1688 then 1 else 2 :=
  nu_p_evenPair (by decide : (1688 : ℕ) ≠ 0) (by decide : Even 1688) hp

theorem nu_p_oneThousandSixHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1690) p = if p = 2 ∨ p ∣ 1690 then 1 else 2 :=
  nu_p_evenPair (by decide : (1690 : ℕ) ≠ 0) (by decide : Even 1690) hp

theorem nu_p_oneThousandSixHundredEightyTwo_two : nu_p (evenPair 1682) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1682)

theorem localFactor_oneThousandSixHundredEightyTwo_two : localFactor (evenPair 1682) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1682 : ℕ) ≠ 0) (by decide : Even 1682)

theorem nu_p_oneThousandSixHundredNinety_two : nu_p (evenPair 1690) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1690)

theorem localFactor_oneThousandSixHundredNinety_two : localFactor (evenPair 1690) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1690 : ℕ) ≠ 0) (by decide : Even 1690)

end Brockian.SingularSeries.Gaps16821690
