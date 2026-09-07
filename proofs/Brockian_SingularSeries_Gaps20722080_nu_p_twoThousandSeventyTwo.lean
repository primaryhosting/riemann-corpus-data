/-
  Brockian/SingularSeriesGaps20722080.lean — even binary gaps n ∈ {2072, 2074, 2076, 2078, 2080}.

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

namespace Brockian.SingularSeries.Gaps20722080

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandSeventyTwo : (evenPair 2072).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2072 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSeventyFour : (evenPair 2074).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2074 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSeventySix : (evenPair 2076).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2076 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSeventyEight : (evenPair 2078).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2078 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandEighty : (evenPair 2080).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2080 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandSeventyTwo : IsAdmissible (evenPair 2072) :=
  isAdmissible_evenPair (by decide : Even 2072)

theorem isAdmissible_evenPair_twoThousandSeventyFour : IsAdmissible (evenPair 2074) :=
  isAdmissible_evenPair (by decide : Even 2074)

theorem isAdmissible_evenPair_twoThousandSeventySix : IsAdmissible (evenPair 2076) :=
  isAdmissible_evenPair (by decide : Even 2076)

theorem isAdmissible_evenPair_twoThousandSeventyEight : IsAdmissible (evenPair 2078) :=
  isAdmissible_evenPair (by decide : Even 2078)

theorem isAdmissible_evenPair_twoThousandEighty : IsAdmissible (evenPair 2080) :=
  isAdmissible_evenPair (by decide : Even 2080)

theorem singular_series_pos_evenPair_twoThousandSeventyTwo : 0 < singularSeries (evenPair 2072) :=
  singular_series_pos_evenPair (by decide : Even 2072)

theorem singular_series_pos_evenPair_twoThousandSeventyFour : 0 < singularSeries (evenPair 2074) :=
  singular_series_pos_evenPair (by decide : Even 2074)

theorem singular_series_pos_evenPair_twoThousandSeventySix : 0 < singularSeries (evenPair 2076) :=
  singular_series_pos_evenPair (by decide : Even 2076)

theorem singular_series_pos_evenPair_twoThousandSeventyEight : 0 < singularSeries (evenPair 2078) :=
  singular_series_pos_evenPair (by decide : Even 2078)

theorem singular_series_pos_evenPair_twoThousandEighty : 0 < singularSeries (evenPair 2080) :=
  singular_series_pos_evenPair (by decide : Even 2080)

theorem singular_series_finite_pos_evenPair_twoThousandSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2072) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2072) P

theorem singular_series_finite_pos_evenPair_twoThousandSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2074) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2074) P

theorem singular_series_finite_pos_evenPair_twoThousandSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2076) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2076) P

theorem singular_series_finite_pos_evenPair_twoThousandSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2078) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2078) P

theorem singular_series_finite_pos_evenPair_twoThousandEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2080) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2080) P

theorem nu_p_twoThousandSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2072) p = if p = 2 ∨ p ∣ 2072 then 1 else 2 :=
  nu_p_evenPair (by decide : (2072 : ℕ) ≠ 0) (by decide : Even 2072) hp

theorem nu_p_twoThousandSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2074) p = if p = 2 ∨ p ∣ 2074 then 1 else 2 :=
  nu_p_evenPair (by decide : (2074 : ℕ) ≠ 0) (by decide : Even 2074) hp

theorem nu_p_twoThousandSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2076) p = if p = 2 ∨ p ∣ 2076 then 1 else 2 :=
  nu_p_evenPair (by decide : (2076 : ℕ) ≠ 0) (by decide : Even 2076) hp

theorem nu_p_twoThousandSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2078) p = if p = 2 ∨ p ∣ 2078 then 1 else 2 :=
  nu_p_evenPair (by decide : (2078 : ℕ) ≠ 0) (by decide : Even 2078) hp

theorem nu_p_twoThousandEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2080) p = if p = 2 ∨ p ∣ 2080 then 1 else 2 :=
  nu_p_evenPair (by decide : (2080 : ℕ) ≠ 0) (by decide : Even 2080) hp

theorem nu_p_twoThousandSeventyTwo_two : nu_p (evenPair 2072) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2072)

theorem localFactor_twoThousandSeventyTwo_two : localFactor (evenPair 2072) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2072 : ℕ) ≠ 0) (by decide : Even 2072)

theorem nu_p_twoThousandEighty_two : nu_p (evenPair 2080) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2080)

theorem localFactor_twoThousandEighty_two : localFactor (evenPair 2080) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2080 : ℕ) ≠ 0) (by decide : Even 2080)

end Brockian.SingularSeries.Gaps20722080
