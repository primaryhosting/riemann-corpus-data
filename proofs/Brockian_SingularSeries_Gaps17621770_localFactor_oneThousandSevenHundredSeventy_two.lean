/-
  Brockian/SingularSeriesGaps17621770.lean — even binary gaps n ∈ {1762, 1764, 1766, 1768, 1770}.

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

namespace Brockian.SingularSeries.Gaps17621770

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredSixtyTwo : (evenPair 1762).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1762 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSixtyFour : (evenPair 1764).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1764 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSixtySix : (evenPair 1766).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1766 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSixtyEight : (evenPair 1768).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1768 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSeventy : (evenPair 1770).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1770 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredSixtyTwo : IsAdmissible (evenPair 1762) :=
  isAdmissible_evenPair (by decide : Even 1762)

theorem isAdmissible_evenPair_oneThousandSevenHundredSixtyFour : IsAdmissible (evenPair 1764) :=
  isAdmissible_evenPair (by decide : Even 1764)

theorem isAdmissible_evenPair_oneThousandSevenHundredSixtySix : IsAdmissible (evenPair 1766) :=
  isAdmissible_evenPair (by decide : Even 1766)

theorem isAdmissible_evenPair_oneThousandSevenHundredSixtyEight : IsAdmissible (evenPair 1768) :=
  isAdmissible_evenPair (by decide : Even 1768)

theorem isAdmissible_evenPair_oneThousandSevenHundredSeventy : IsAdmissible (evenPair 1770) :=
  isAdmissible_evenPair (by decide : Even 1770)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSixtyTwo : 0 < singularSeries (evenPair 1762) :=
  singular_series_pos_evenPair (by decide : Even 1762)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSixtyFour : 0 < singularSeries (evenPair 1764) :=
  singular_series_pos_evenPair (by decide : Even 1764)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSixtySix : 0 < singularSeries (evenPair 1766) :=
  singular_series_pos_evenPair (by decide : Even 1766)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSixtyEight : 0 < singularSeries (evenPair 1768) :=
  singular_series_pos_evenPair (by decide : Even 1768)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSeventy : 0 < singularSeries (evenPair 1770) :=
  singular_series_pos_evenPair (by decide : Even 1770)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1762) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1762) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1764) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1764) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1766) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1766) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1768) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1768) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1770) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1770) P

theorem nu_p_oneThousandSevenHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1762) p = if p = 2 ∨ p ∣ 1762 then 1 else 2 :=
  nu_p_evenPair (by decide : (1762 : ℕ) ≠ 0) (by decide : Even 1762) hp

theorem nu_p_oneThousandSevenHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1764) p = if p = 2 ∨ p ∣ 1764 then 1 else 2 :=
  nu_p_evenPair (by decide : (1764 : ℕ) ≠ 0) (by decide : Even 1764) hp

theorem nu_p_oneThousandSevenHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1766) p = if p = 2 ∨ p ∣ 1766 then 1 else 2 :=
  nu_p_evenPair (by decide : (1766 : ℕ) ≠ 0) (by decide : Even 1766) hp

theorem nu_p_oneThousandSevenHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1768) p = if p = 2 ∨ p ∣ 1768 then 1 else 2 :=
  nu_p_evenPair (by decide : (1768 : ℕ) ≠ 0) (by decide : Even 1768) hp

theorem nu_p_oneThousandSevenHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1770) p = if p = 2 ∨ p ∣ 1770 then 1 else 2 :=
  nu_p_evenPair (by decide : (1770 : ℕ) ≠ 0) (by decide : Even 1770) hp

theorem nu_p_oneThousandSevenHundredSixtyTwo_two : nu_p (evenPair 1762) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1762)

theorem localFactor_oneThousandSevenHundredSixtyTwo_two : localFactor (evenPair 1762) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1762 : ℕ) ≠ 0) (by decide : Even 1762)

theorem nu_p_oneThousandSevenHundredSeventy_two : nu_p (evenPair 1770) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1770)

theorem localFactor_oneThousandSevenHundredSeventy_two : localFactor (evenPair 1770) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1770 : ℕ) ≠ 0) (by decide : Even 1770)

end Brockian.SingularSeries.Gaps17621770
