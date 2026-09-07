/-
  Brockian/SingularSeriesGaps10021010.lean — even binary gaps n ∈ {1002, 1004, 1006, 1008, 1010}.

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

namespace Brockian.SingularSeries.Gaps10021010

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwo : (evenPair 1002).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1002 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFour : (evenPair 1004).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1004 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSix : (evenPair 1006).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1006 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEight : (evenPair 1008).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1008 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTen : (evenPair 1010).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1010 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwo : IsAdmissible (evenPair 1002) :=
  isAdmissible_evenPair (by decide : Even 1002)

theorem isAdmissible_evenPair_oneThousandFour : IsAdmissible (evenPair 1004) :=
  isAdmissible_evenPair (by decide : Even 1004)

theorem isAdmissible_evenPair_oneThousandSix : IsAdmissible (evenPair 1006) :=
  isAdmissible_evenPair (by decide : Even 1006)

theorem isAdmissible_evenPair_oneThousandEight : IsAdmissible (evenPair 1008) :=
  isAdmissible_evenPair (by decide : Even 1008)

theorem isAdmissible_evenPair_oneThousandTen : IsAdmissible (evenPair 1010) :=
  isAdmissible_evenPair (by decide : Even 1010)

theorem singular_series_pos_evenPair_oneThousandTwo : 0 < singularSeries (evenPair 1002) :=
  singular_series_pos_evenPair (by decide : Even 1002)

theorem singular_series_pos_evenPair_oneThousandFour : 0 < singularSeries (evenPair 1004) :=
  singular_series_pos_evenPair (by decide : Even 1004)

theorem singular_series_pos_evenPair_oneThousandSix : 0 < singularSeries (evenPair 1006) :=
  singular_series_pos_evenPair (by decide : Even 1006)

theorem singular_series_pos_evenPair_oneThousandEight : 0 < singularSeries (evenPair 1008) :=
  singular_series_pos_evenPair (by decide : Even 1008)

theorem singular_series_pos_evenPair_oneThousandTen : 0 < singularSeries (evenPair 1010) :=
  singular_series_pos_evenPair (by decide : Even 1010)

theorem singular_series_finite_pos_evenPair_oneThousandTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1002) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1002) P

theorem singular_series_finite_pos_evenPair_oneThousandFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1004) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1004) P

theorem singular_series_finite_pos_evenPair_oneThousandSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1006) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1006) P

theorem singular_series_finite_pos_evenPair_oneThousandEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1008) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1008) P

theorem singular_series_finite_pos_evenPair_oneThousandTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1010) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1010) P

theorem nu_p_oneThousandTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1002) p = if p = 2 ∨ p ∣ 1002 then 1 else 2 :=
  nu_p_evenPair (by decide : (1002 : ℕ) ≠ 0) (by decide : Even 1002) hp

theorem nu_p_oneThousandFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1004) p = if p = 2 ∨ p ∣ 1004 then 1 else 2 :=
  nu_p_evenPair (by decide : (1004 : ℕ) ≠ 0) (by decide : Even 1004) hp

theorem nu_p_oneThousandSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1006) p = if p = 2 ∨ p ∣ 1006 then 1 else 2 :=
  nu_p_evenPair (by decide : (1006 : ℕ) ≠ 0) (by decide : Even 1006) hp

theorem nu_p_oneThousandEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1008) p = if p = 2 ∨ p ∣ 1008 then 1 else 2 :=
  nu_p_evenPair (by decide : (1008 : ℕ) ≠ 0) (by decide : Even 1008) hp

theorem nu_p_oneThousandTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1010) p = if p = 2 ∨ p ∣ 1010 then 1 else 2 :=
  nu_p_evenPair (by decide : (1010 : ℕ) ≠ 0) (by decide : Even 1010) hp

theorem nu_p_oneThousandTwo_two : nu_p (evenPair 1002) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1002)

theorem localFactor_oneThousandTwo_two : localFactor (evenPair 1002) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1002 : ℕ) ≠ 0) (by decide : Even 1002)

theorem nu_p_oneThousandTen_two : nu_p (evenPair 1010) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1010)

theorem localFactor_oneThousandTen_two : localFactor (evenPair 1010) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1010 : ℕ) ≠ 0) (by decide : Even 1010)

end Brockian.SingularSeries.Gaps10021010
