/-
  Brockian/SingularSeriesGaps10721080.lean — even binary gaps n ∈ {1072, 1074, 1076, 1078, 1080}.

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

namespace Brockian.SingularSeries.Gaps10721080

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSeventyTwo : (evenPair 1072).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1072 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSeventyFour : (evenPair 1074).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1074 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSeventySix : (evenPair 1076).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1076 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSeventyEight : (evenPair 1078).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1078 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEighty : (evenPair 1080).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1080 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSeventyTwo : IsAdmissible (evenPair 1072) :=
  isAdmissible_evenPair (by decide : Even 1072)

theorem isAdmissible_evenPair_oneThousandSeventyFour : IsAdmissible (evenPair 1074) :=
  isAdmissible_evenPair (by decide : Even 1074)

theorem isAdmissible_evenPair_oneThousandSeventySix : IsAdmissible (evenPair 1076) :=
  isAdmissible_evenPair (by decide : Even 1076)

theorem isAdmissible_evenPair_oneThousandSeventyEight : IsAdmissible (evenPair 1078) :=
  isAdmissible_evenPair (by decide : Even 1078)

theorem isAdmissible_evenPair_oneThousandEighty : IsAdmissible (evenPair 1080) :=
  isAdmissible_evenPair (by decide : Even 1080)

theorem singular_series_pos_evenPair_oneThousandSeventyTwo : 0 < singularSeries (evenPair 1072) :=
  singular_series_pos_evenPair (by decide : Even 1072)

theorem singular_series_pos_evenPair_oneThousandSeventyFour : 0 < singularSeries (evenPair 1074) :=
  singular_series_pos_evenPair (by decide : Even 1074)

theorem singular_series_pos_evenPair_oneThousandSeventySix : 0 < singularSeries (evenPair 1076) :=
  singular_series_pos_evenPair (by decide : Even 1076)

theorem singular_series_pos_evenPair_oneThousandSeventyEight : 0 < singularSeries (evenPair 1078) :=
  singular_series_pos_evenPair (by decide : Even 1078)

theorem singular_series_pos_evenPair_oneThousandEighty : 0 < singularSeries (evenPair 1080) :=
  singular_series_pos_evenPair (by decide : Even 1080)

theorem singular_series_finite_pos_evenPair_oneThousandSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1072) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1072) P

theorem singular_series_finite_pos_evenPair_oneThousandSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1074) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1074) P

theorem singular_series_finite_pos_evenPair_oneThousandSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1076) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1076) P

theorem singular_series_finite_pos_evenPair_oneThousandSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1078) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1078) P

theorem singular_series_finite_pos_evenPair_oneThousandEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1080) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1080) P

theorem nu_p_oneThousandSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1072) p = if p = 2 ∨ p ∣ 1072 then 1 else 2 :=
  nu_p_evenPair (by decide : (1072 : ℕ) ≠ 0) (by decide : Even 1072) hp

theorem nu_p_oneThousandSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1074) p = if p = 2 ∨ p ∣ 1074 then 1 else 2 :=
  nu_p_evenPair (by decide : (1074 : ℕ) ≠ 0) (by decide : Even 1074) hp

theorem nu_p_oneThousandSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1076) p = if p = 2 ∨ p ∣ 1076 then 1 else 2 :=
  nu_p_evenPair (by decide : (1076 : ℕ) ≠ 0) (by decide : Even 1076) hp

theorem nu_p_oneThousandSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1078) p = if p = 2 ∨ p ∣ 1078 then 1 else 2 :=
  nu_p_evenPair (by decide : (1078 : ℕ) ≠ 0) (by decide : Even 1078) hp

theorem nu_p_oneThousandEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1080) p = if p = 2 ∨ p ∣ 1080 then 1 else 2 :=
  nu_p_evenPair (by decide : (1080 : ℕ) ≠ 0) (by decide : Even 1080) hp

theorem nu_p_oneThousandSeventyTwo_two : nu_p (evenPair 1072) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1072)

theorem localFactor_oneThousandSeventyTwo_two : localFactor (evenPair 1072) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1072 : ℕ) ≠ 0) (by decide : Even 1072)

theorem nu_p_oneThousandEighty_two : nu_p (evenPair 1080) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1080)

theorem localFactor_oneThousandEighty_two : localFactor (evenPair 1080) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1080 : ℕ) ≠ 0) (by decide : Even 1080)

end Brockian.SingularSeries.Gaps10721080
