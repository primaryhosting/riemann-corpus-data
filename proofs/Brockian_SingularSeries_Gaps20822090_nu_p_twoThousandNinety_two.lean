/-
  Brockian/SingularSeriesGaps20822090.lean — even binary gaps n ∈ {2082, 2084, 2086, 2088, 2090}.

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

namespace Brockian.SingularSeries.Gaps20822090

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandEightyTwo : (evenPair 2082).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2082 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandEightyFour : (evenPair 2084).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2084 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandEightySix : (evenPair 2086).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2086 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandEightyEight : (evenPair 2088).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2088 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandNinety : (evenPair 2090).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2090 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandEightyTwo : IsAdmissible (evenPair 2082) :=
  isAdmissible_evenPair (by decide : Even 2082)

theorem isAdmissible_evenPair_twoThousandEightyFour : IsAdmissible (evenPair 2084) :=
  isAdmissible_evenPair (by decide : Even 2084)

theorem isAdmissible_evenPair_twoThousandEightySix : IsAdmissible (evenPair 2086) :=
  isAdmissible_evenPair (by decide : Even 2086)

theorem isAdmissible_evenPair_twoThousandEightyEight : IsAdmissible (evenPair 2088) :=
  isAdmissible_evenPair (by decide : Even 2088)

theorem isAdmissible_evenPair_twoThousandNinety : IsAdmissible (evenPair 2090) :=
  isAdmissible_evenPair (by decide : Even 2090)

theorem singular_series_pos_evenPair_twoThousandEightyTwo : 0 < singularSeries (evenPair 2082) :=
  singular_series_pos_evenPair (by decide : Even 2082)

theorem singular_series_pos_evenPair_twoThousandEightyFour : 0 < singularSeries (evenPair 2084) :=
  singular_series_pos_evenPair (by decide : Even 2084)

theorem singular_series_pos_evenPair_twoThousandEightySix : 0 < singularSeries (evenPair 2086) :=
  singular_series_pos_evenPair (by decide : Even 2086)

theorem singular_series_pos_evenPair_twoThousandEightyEight : 0 < singularSeries (evenPair 2088) :=
  singular_series_pos_evenPair (by decide : Even 2088)

theorem singular_series_pos_evenPair_twoThousandNinety : 0 < singularSeries (evenPair 2090) :=
  singular_series_pos_evenPair (by decide : Even 2090)

theorem singular_series_finite_pos_evenPair_twoThousandEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2082) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2082) P

theorem singular_series_finite_pos_evenPair_twoThousandEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2084) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2084) P

theorem singular_series_finite_pos_evenPair_twoThousandEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2086) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2086) P

theorem singular_series_finite_pos_evenPair_twoThousandEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2088) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2088) P

theorem singular_series_finite_pos_evenPair_twoThousandNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2090) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2090) P

theorem nu_p_twoThousandEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2082) p = if p = 2 ∨ p ∣ 2082 then 1 else 2 :=
  nu_p_evenPair (by decide : (2082 : ℕ) ≠ 0) (by decide : Even 2082) hp

theorem nu_p_twoThousandEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2084) p = if p = 2 ∨ p ∣ 2084 then 1 else 2 :=
  nu_p_evenPair (by decide : (2084 : ℕ) ≠ 0) (by decide : Even 2084) hp

theorem nu_p_twoThousandEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2086) p = if p = 2 ∨ p ∣ 2086 then 1 else 2 :=
  nu_p_evenPair (by decide : (2086 : ℕ) ≠ 0) (by decide : Even 2086) hp

theorem nu_p_twoThousandEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2088) p = if p = 2 ∨ p ∣ 2088 then 1 else 2 :=
  nu_p_evenPair (by decide : (2088 : ℕ) ≠ 0) (by decide : Even 2088) hp

theorem nu_p_twoThousandNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2090) p = if p = 2 ∨ p ∣ 2090 then 1 else 2 :=
  nu_p_evenPair (by decide : (2090 : ℕ) ≠ 0) (by decide : Even 2090) hp

theorem nu_p_twoThousandEightyTwo_two : nu_p (evenPair 2082) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2082)

theorem localFactor_twoThousandEightyTwo_two : localFactor (evenPair 2082) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2082 : ℕ) ≠ 0) (by decide : Even 2082)

theorem nu_p_twoThousandNinety_two : nu_p (evenPair 2090) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2090)

theorem localFactor_twoThousandNinety_two : localFactor (evenPair 2090) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2090 : ℕ) ≠ 0) (by decide : Even 2090)

end Brockian.SingularSeries.Gaps20822090
