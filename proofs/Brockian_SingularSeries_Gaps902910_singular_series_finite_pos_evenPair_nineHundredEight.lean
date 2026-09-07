/-
  Brockian/SingularSeriesGaps902910.lean — even binary gaps n ∈ {902, 904, 906, 908, 910}.

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

namespace Brockian.SingularSeries.Gaps902910

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredTwo : (evenPair 902).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (902 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredFour : (evenPair 904).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (904 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSix : (evenPair 906).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (906 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredEight : (evenPair 908).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (908 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredTen : (evenPair 910).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (910 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredTwo : IsAdmissible (evenPair 902) :=
  isAdmissible_evenPair (by decide : Even 902)

theorem isAdmissible_evenPair_nineHundredFour : IsAdmissible (evenPair 904) :=
  isAdmissible_evenPair (by decide : Even 904)

theorem isAdmissible_evenPair_nineHundredSix : IsAdmissible (evenPair 906) :=
  isAdmissible_evenPair (by decide : Even 906)

theorem isAdmissible_evenPair_nineHundredEight : IsAdmissible (evenPair 908) :=
  isAdmissible_evenPair (by decide : Even 908)

theorem isAdmissible_evenPair_nineHundredTen : IsAdmissible (evenPair 910) :=
  isAdmissible_evenPair (by decide : Even 910)

theorem singular_series_pos_evenPair_nineHundredTwo : 0 < singularSeries (evenPair 902) :=
  singular_series_pos_evenPair (by decide : Even 902)

theorem singular_series_pos_evenPair_nineHundredFour : 0 < singularSeries (evenPair 904) :=
  singular_series_pos_evenPair (by decide : Even 904)

theorem singular_series_pos_evenPair_nineHundredSix : 0 < singularSeries (evenPair 906) :=
  singular_series_pos_evenPair (by decide : Even 906)

theorem singular_series_pos_evenPair_nineHundredEight : 0 < singularSeries (evenPair 908) :=
  singular_series_pos_evenPair (by decide : Even 908)

theorem singular_series_pos_evenPair_nineHundredTen : 0 < singularSeries (evenPair 910) :=
  singular_series_pos_evenPair (by decide : Even 910)

theorem singular_series_finite_pos_evenPair_nineHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 902) P :=
  singular_series_finite_pos_evenPair (by decide : Even 902) P

theorem singular_series_finite_pos_evenPair_nineHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 904) P :=
  singular_series_finite_pos_evenPair (by decide : Even 904) P

theorem singular_series_finite_pos_evenPair_nineHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 906) P :=
  singular_series_finite_pos_evenPair (by decide : Even 906) P

theorem singular_series_finite_pos_evenPair_nineHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 908) P :=
  singular_series_finite_pos_evenPair (by decide : Even 908) P

theorem singular_series_finite_pos_evenPair_nineHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 910) P :=
  singular_series_finite_pos_evenPair (by decide : Even 910) P

theorem nu_p_nineHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 902) p = if p = 2 ∨ p ∣ 902 then 1 else 2 :=
  nu_p_evenPair (by decide : (902 : ℕ) ≠ 0) (by decide : Even 902) hp

theorem nu_p_nineHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 904) p = if p = 2 ∨ p ∣ 904 then 1 else 2 :=
  nu_p_evenPair (by decide : (904 : ℕ) ≠ 0) (by decide : Even 904) hp

theorem nu_p_nineHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 906) p = if p = 2 ∨ p ∣ 906 then 1 else 2 :=
  nu_p_evenPair (by decide : (906 : ℕ) ≠ 0) (by decide : Even 906) hp

theorem nu_p_nineHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 908) p = if p = 2 ∨ p ∣ 908 then 1 else 2 :=
  nu_p_evenPair (by decide : (908 : ℕ) ≠ 0) (by decide : Even 908) hp

theorem nu_p_nineHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 910) p = if p = 2 ∨ p ∣ 910 then 1 else 2 :=
  nu_p_evenPair (by decide : (910 : ℕ) ≠ 0) (by decide : Even 910) hp

theorem nu_p_nineHundredTwo_two : nu_p (evenPair 902) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 902)

theorem localFactor_nineHundredTwo_two : localFactor (evenPair 902) 2 = 2 :=
  localFactor_evenPair_two (by decide : (902 : ℕ) ≠ 0) (by decide : Even 902)

theorem nu_p_nineHundredTen_two : nu_p (evenPair 910) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 910)

theorem localFactor_nineHundredTen_two : localFactor (evenPair 910) 2 = 2 :=
  localFactor_evenPair_two (by decide : (910 : ℕ) ≠ 0) (by decide : Even 910)

end Brockian.SingularSeries.Gaps902910
