/-
  Brockian/SingularSeriesGaps10621070.lean — even binary gaps n ∈ {1062, 1064, 1066, 1068, 1070}.

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

namespace Brockian.SingularSeries.Gaps10621070

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixtyTwo : (evenPair 1062).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1062 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixtyFour : (evenPair 1064).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1064 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixtySix : (evenPair 1066).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1066 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixtyEight : (evenPair 1068).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1068 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSeventy : (evenPair 1070).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1070 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixtyTwo : IsAdmissible (evenPair 1062) :=
  isAdmissible_evenPair (by decide : Even 1062)

theorem isAdmissible_evenPair_oneThousandSixtyFour : IsAdmissible (evenPair 1064) :=
  isAdmissible_evenPair (by decide : Even 1064)

theorem isAdmissible_evenPair_oneThousandSixtySix : IsAdmissible (evenPair 1066) :=
  isAdmissible_evenPair (by decide : Even 1066)

theorem isAdmissible_evenPair_oneThousandSixtyEight : IsAdmissible (evenPair 1068) :=
  isAdmissible_evenPair (by decide : Even 1068)

theorem isAdmissible_evenPair_oneThousandSeventy : IsAdmissible (evenPair 1070) :=
  isAdmissible_evenPair (by decide : Even 1070)

theorem singular_series_pos_evenPair_oneThousandSixtyTwo : 0 < singularSeries (evenPair 1062) :=
  singular_series_pos_evenPair (by decide : Even 1062)

theorem singular_series_pos_evenPair_oneThousandSixtyFour : 0 < singularSeries (evenPair 1064) :=
  singular_series_pos_evenPair (by decide : Even 1064)

theorem singular_series_pos_evenPair_oneThousandSixtySix : 0 < singularSeries (evenPair 1066) :=
  singular_series_pos_evenPair (by decide : Even 1066)

theorem singular_series_pos_evenPair_oneThousandSixtyEight : 0 < singularSeries (evenPair 1068) :=
  singular_series_pos_evenPair (by decide : Even 1068)

theorem singular_series_pos_evenPair_oneThousandSeventy : 0 < singularSeries (evenPair 1070) :=
  singular_series_pos_evenPair (by decide : Even 1070)

theorem singular_series_finite_pos_evenPair_oneThousandSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1062) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1062) P

theorem singular_series_finite_pos_evenPair_oneThousandSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1064) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1064) P

theorem singular_series_finite_pos_evenPair_oneThousandSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1066) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1066) P

theorem singular_series_finite_pos_evenPair_oneThousandSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1068) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1068) P

theorem singular_series_finite_pos_evenPair_oneThousandSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1070) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1070) P

theorem nu_p_oneThousandSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1062) p = if p = 2 ∨ p ∣ 1062 then 1 else 2 :=
  nu_p_evenPair (by decide : (1062 : ℕ) ≠ 0) (by decide : Even 1062) hp

theorem nu_p_oneThousandSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1064) p = if p = 2 ∨ p ∣ 1064 then 1 else 2 :=
  nu_p_evenPair (by decide : (1064 : ℕ) ≠ 0) (by decide : Even 1064) hp

theorem nu_p_oneThousandSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1066) p = if p = 2 ∨ p ∣ 1066 then 1 else 2 :=
  nu_p_evenPair (by decide : (1066 : ℕ) ≠ 0) (by decide : Even 1066) hp

theorem nu_p_oneThousandSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1068) p = if p = 2 ∨ p ∣ 1068 then 1 else 2 :=
  nu_p_evenPair (by decide : (1068 : ℕ) ≠ 0) (by decide : Even 1068) hp

theorem nu_p_oneThousandSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1070) p = if p = 2 ∨ p ∣ 1070 then 1 else 2 :=
  nu_p_evenPair (by decide : (1070 : ℕ) ≠ 0) (by decide : Even 1070) hp

theorem nu_p_oneThousandSixtyTwo_two : nu_p (evenPair 1062) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1062)

theorem localFactor_oneThousandSixtyTwo_two : localFactor (evenPair 1062) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1062 : ℕ) ≠ 0) (by decide : Even 1062)

theorem nu_p_oneThousandSeventy_two : nu_p (evenPair 1070) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1070)

theorem localFactor_oneThousandSeventy_two : localFactor (evenPair 1070) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1070 : ℕ) ≠ 0) (by decide : Even 1070)

end Brockian.SingularSeries.Gaps10621070
