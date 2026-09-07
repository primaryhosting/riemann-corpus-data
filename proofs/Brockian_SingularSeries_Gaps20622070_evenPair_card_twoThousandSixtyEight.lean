/-
  Brockian/SingularSeriesGaps20622070.lean — even binary gaps n ∈ {2062, 2064, 2066, 2068, 2070}.

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

namespace Brockian.SingularSeries.Gaps20622070

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandSixtyTwo : (evenPair 2062).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2062 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSixtyFour : (evenPair 2064).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2064 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSixtySix : (evenPair 2066).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2066 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSixtyEight : (evenPair 2068).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2068 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSeventy : (evenPair 2070).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2070 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandSixtyTwo : IsAdmissible (evenPair 2062) :=
  isAdmissible_evenPair (by decide : Even 2062)

theorem isAdmissible_evenPair_twoThousandSixtyFour : IsAdmissible (evenPair 2064) :=
  isAdmissible_evenPair (by decide : Even 2064)

theorem isAdmissible_evenPair_twoThousandSixtySix : IsAdmissible (evenPair 2066) :=
  isAdmissible_evenPair (by decide : Even 2066)

theorem isAdmissible_evenPair_twoThousandSixtyEight : IsAdmissible (evenPair 2068) :=
  isAdmissible_evenPair (by decide : Even 2068)

theorem isAdmissible_evenPair_twoThousandSeventy : IsAdmissible (evenPair 2070) :=
  isAdmissible_evenPair (by decide : Even 2070)

theorem singular_series_pos_evenPair_twoThousandSixtyTwo : 0 < singularSeries (evenPair 2062) :=
  singular_series_pos_evenPair (by decide : Even 2062)

theorem singular_series_pos_evenPair_twoThousandSixtyFour : 0 < singularSeries (evenPair 2064) :=
  singular_series_pos_evenPair (by decide : Even 2064)

theorem singular_series_pos_evenPair_twoThousandSixtySix : 0 < singularSeries (evenPair 2066) :=
  singular_series_pos_evenPair (by decide : Even 2066)

theorem singular_series_pos_evenPair_twoThousandSixtyEight : 0 < singularSeries (evenPair 2068) :=
  singular_series_pos_evenPair (by decide : Even 2068)

theorem singular_series_pos_evenPair_twoThousandSeventy : 0 < singularSeries (evenPair 2070) :=
  singular_series_pos_evenPair (by decide : Even 2070)

theorem singular_series_finite_pos_evenPair_twoThousandSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2062) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2062) P

theorem singular_series_finite_pos_evenPair_twoThousandSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2064) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2064) P

theorem singular_series_finite_pos_evenPair_twoThousandSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2066) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2066) P

theorem singular_series_finite_pos_evenPair_twoThousandSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2068) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2068) P

theorem singular_series_finite_pos_evenPair_twoThousandSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2070) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2070) P

theorem nu_p_twoThousandSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2062) p = if p = 2 ∨ p ∣ 2062 then 1 else 2 :=
  nu_p_evenPair (by decide : (2062 : ℕ) ≠ 0) (by decide : Even 2062) hp

theorem nu_p_twoThousandSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2064) p = if p = 2 ∨ p ∣ 2064 then 1 else 2 :=
  nu_p_evenPair (by decide : (2064 : ℕ) ≠ 0) (by decide : Even 2064) hp

theorem nu_p_twoThousandSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2066) p = if p = 2 ∨ p ∣ 2066 then 1 else 2 :=
  nu_p_evenPair (by decide : (2066 : ℕ) ≠ 0) (by decide : Even 2066) hp

theorem nu_p_twoThousandSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2068) p = if p = 2 ∨ p ∣ 2068 then 1 else 2 :=
  nu_p_evenPair (by decide : (2068 : ℕ) ≠ 0) (by decide : Even 2068) hp

theorem nu_p_twoThousandSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2070) p = if p = 2 ∨ p ∣ 2070 then 1 else 2 :=
  nu_p_evenPair (by decide : (2070 : ℕ) ≠ 0) (by decide : Even 2070) hp

theorem nu_p_twoThousandSixtyTwo_two : nu_p (evenPair 2062) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2062)

theorem localFactor_twoThousandSixtyTwo_two : localFactor (evenPair 2062) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2062 : ℕ) ≠ 0) (by decide : Even 2062)

theorem nu_p_twoThousandSeventy_two : nu_p (evenPair 2070) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2070)

theorem localFactor_twoThousandSeventy_two : localFactor (evenPair 2070) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2070 : ℕ) ≠ 0) (by decide : Even 2070)

end Brockian.SingularSeries.Gaps20622070
