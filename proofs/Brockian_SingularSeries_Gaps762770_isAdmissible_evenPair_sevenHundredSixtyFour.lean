/-
  Brockian/SingularSeriesGaps762770.lean — even binary gaps n ∈ {762, 764, 766, 768, 770}.

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

namespace Brockian.SingularSeries.Gaps762770

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredSixtyTwo : (evenPair 762).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (762 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSixtyFour : (evenPair 764).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (764 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSixtySix : (evenPair 766).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (766 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSixtyEight : (evenPair 768).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (768 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSeventy : (evenPair 770).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (770 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredSixtyTwo : IsAdmissible (evenPair 762) :=
  isAdmissible_evenPair (by decide : Even 762)

theorem isAdmissible_evenPair_sevenHundredSixtyFour : IsAdmissible (evenPair 764) :=
  isAdmissible_evenPair (by decide : Even 764)

theorem isAdmissible_evenPair_sevenHundredSixtySix : IsAdmissible (evenPair 766) :=
  isAdmissible_evenPair (by decide : Even 766)

theorem isAdmissible_evenPair_sevenHundredSixtyEight : IsAdmissible (evenPair 768) :=
  isAdmissible_evenPair (by decide : Even 768)

theorem isAdmissible_evenPair_sevenHundredSeventy : IsAdmissible (evenPair 770) :=
  isAdmissible_evenPair (by decide : Even 770)

theorem singular_series_pos_evenPair_sevenHundredSixtyTwo : 0 < singularSeries (evenPair 762) :=
  singular_series_pos_evenPair (by decide : Even 762)

theorem singular_series_pos_evenPair_sevenHundredSixtyFour : 0 < singularSeries (evenPair 764) :=
  singular_series_pos_evenPair (by decide : Even 764)

theorem singular_series_pos_evenPair_sevenHundredSixtySix : 0 < singularSeries (evenPair 766) :=
  singular_series_pos_evenPair (by decide : Even 766)

theorem singular_series_pos_evenPair_sevenHundredSixtyEight : 0 < singularSeries (evenPair 768) :=
  singular_series_pos_evenPair (by decide : Even 768)

theorem singular_series_pos_evenPair_sevenHundredSeventy : 0 < singularSeries (evenPair 770) :=
  singular_series_pos_evenPair (by decide : Even 770)

theorem singular_series_finite_pos_evenPair_sevenHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 762) P :=
  singular_series_finite_pos_evenPair (by decide : Even 762) P

theorem singular_series_finite_pos_evenPair_sevenHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 764) P :=
  singular_series_finite_pos_evenPair (by decide : Even 764) P

theorem singular_series_finite_pos_evenPair_sevenHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 766) P :=
  singular_series_finite_pos_evenPair (by decide : Even 766) P

theorem singular_series_finite_pos_evenPair_sevenHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 768) P :=
  singular_series_finite_pos_evenPair (by decide : Even 768) P

theorem singular_series_finite_pos_evenPair_sevenHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 770) P :=
  singular_series_finite_pos_evenPair (by decide : Even 770) P

theorem nu_p_sevenHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 762) p = if p = 2 ∨ p ∣ 762 then 1 else 2 :=
  nu_p_evenPair (by decide : (762 : ℕ) ≠ 0) (by decide : Even 762) hp

theorem nu_p_sevenHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 764) p = if p = 2 ∨ p ∣ 764 then 1 else 2 :=
  nu_p_evenPair (by decide : (764 : ℕ) ≠ 0) (by decide : Even 764) hp

theorem nu_p_sevenHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 766) p = if p = 2 ∨ p ∣ 766 then 1 else 2 :=
  nu_p_evenPair (by decide : (766 : ℕ) ≠ 0) (by decide : Even 766) hp

theorem nu_p_sevenHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 768) p = if p = 2 ∨ p ∣ 768 then 1 else 2 :=
  nu_p_evenPair (by decide : (768 : ℕ) ≠ 0) (by decide : Even 768) hp

theorem nu_p_sevenHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 770) p = if p = 2 ∨ p ∣ 770 then 1 else 2 :=
  nu_p_evenPair (by decide : (770 : ℕ) ≠ 0) (by decide : Even 770) hp

theorem nu_p_sevenHundredSixtyTwo_two : nu_p (evenPair 762) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 762)

theorem localFactor_sevenHundredSixtyTwo_two : localFactor (evenPair 762) 2 = 2 :=
  localFactor_evenPair_two (by decide : (762 : ℕ) ≠ 0) (by decide : Even 762)

theorem nu_p_sevenHundredSeventy_two : nu_p (evenPair 770) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 770)

theorem localFactor_sevenHundredSeventy_two : localFactor (evenPair 770) 2 = 2 :=
  localFactor_evenPair_two (by decide : (770 : ℕ) ≠ 0) (by decide : Even 770)

end Brockian.SingularSeries.Gaps762770
