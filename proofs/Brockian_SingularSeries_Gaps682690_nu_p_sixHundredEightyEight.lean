/-
  Brockian/SingularSeriesGaps682690.lean — even binary gaps n ∈ {682, 684, 686, 688, 690}.

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

namespace Brockian.SingularSeries.Gaps682690

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredEightyTwo : (evenPair 682).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (682 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredEightyFour : (evenPair 684).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (684 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredEightySix : (evenPair 686).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (686 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredEightyEight : (evenPair 688).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (688 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredNinety : (evenPair 690).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (690 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredEightyTwo : IsAdmissible (evenPair 682) :=
  isAdmissible_evenPair (by decide : Even 682)

theorem isAdmissible_evenPair_sixHundredEightyFour : IsAdmissible (evenPair 684) :=
  isAdmissible_evenPair (by decide : Even 684)

theorem isAdmissible_evenPair_sixHundredEightySix : IsAdmissible (evenPair 686) :=
  isAdmissible_evenPair (by decide : Even 686)

theorem isAdmissible_evenPair_sixHundredEightyEight : IsAdmissible (evenPair 688) :=
  isAdmissible_evenPair (by decide : Even 688)

theorem isAdmissible_evenPair_sixHundredNinety : IsAdmissible (evenPair 690) :=
  isAdmissible_evenPair (by decide : Even 690)

theorem singular_series_pos_evenPair_sixHundredEightyTwo : 0 < singularSeries (evenPair 682) :=
  singular_series_pos_evenPair (by decide : Even 682)

theorem singular_series_pos_evenPair_sixHundredEightyFour : 0 < singularSeries (evenPair 684) :=
  singular_series_pos_evenPair (by decide : Even 684)

theorem singular_series_pos_evenPair_sixHundredEightySix : 0 < singularSeries (evenPair 686) :=
  singular_series_pos_evenPair (by decide : Even 686)

theorem singular_series_pos_evenPair_sixHundredEightyEight : 0 < singularSeries (evenPair 688) :=
  singular_series_pos_evenPair (by decide : Even 688)

theorem singular_series_pos_evenPair_sixHundredNinety : 0 < singularSeries (evenPair 690) :=
  singular_series_pos_evenPair (by decide : Even 690)

theorem singular_series_finite_pos_evenPair_sixHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 682) P :=
  singular_series_finite_pos_evenPair (by decide : Even 682) P

theorem singular_series_finite_pos_evenPair_sixHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 684) P :=
  singular_series_finite_pos_evenPair (by decide : Even 684) P

theorem singular_series_finite_pos_evenPair_sixHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 686) P :=
  singular_series_finite_pos_evenPair (by decide : Even 686) P

theorem singular_series_finite_pos_evenPair_sixHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 688) P :=
  singular_series_finite_pos_evenPair (by decide : Even 688) P

theorem singular_series_finite_pos_evenPair_sixHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 690) P :=
  singular_series_finite_pos_evenPair (by decide : Even 690) P

theorem nu_p_sixHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 682) p = if p = 2 ∨ p ∣ 682 then 1 else 2 :=
  nu_p_evenPair (by decide : (682 : ℕ) ≠ 0) (by decide : Even 682) hp

theorem nu_p_sixHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 684) p = if p = 2 ∨ p ∣ 684 then 1 else 2 :=
  nu_p_evenPair (by decide : (684 : ℕ) ≠ 0) (by decide : Even 684) hp

theorem nu_p_sixHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 686) p = if p = 2 ∨ p ∣ 686 then 1 else 2 :=
  nu_p_evenPair (by decide : (686 : ℕ) ≠ 0) (by decide : Even 686) hp

theorem nu_p_sixHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 688) p = if p = 2 ∨ p ∣ 688 then 1 else 2 :=
  nu_p_evenPair (by decide : (688 : ℕ) ≠ 0) (by decide : Even 688) hp

theorem nu_p_sixHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 690) p = if p = 2 ∨ p ∣ 690 then 1 else 2 :=
  nu_p_evenPair (by decide : (690 : ℕ) ≠ 0) (by decide : Even 690) hp

theorem nu_p_sixHundredEightyTwo_two : nu_p (evenPair 682) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 682)

theorem localFactor_sixHundredEightyTwo_two : localFactor (evenPair 682) 2 = 2 :=
  localFactor_evenPair_two (by decide : (682 : ℕ) ≠ 0) (by decide : Even 682)

theorem nu_p_sixHundredNinety_two : nu_p (evenPair 690) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 690)

theorem localFactor_sixHundredNinety_two : localFactor (evenPair 690) 2 = 2 :=
  localFactor_evenPair_two (by decide : (690 : ℕ) ≠ 0) (by decide : Even 690)

end Brockian.SingularSeries.Gaps682690
