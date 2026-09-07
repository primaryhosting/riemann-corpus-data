/-
  Brockian/SingularSeriesGaps11721180.lean — even binary gaps n ∈ {1172, 1174, 1176, 1178, 1180}.

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

namespace Brockian.SingularSeries.Gaps11721180

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredSeventyTwo : (evenPair 1172).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1172 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSeventyFour : (evenPair 1174).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1174 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSeventySix : (evenPair 1176).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1176 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSeventyEight : (evenPair 1178).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1178 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredEighty : (evenPair 1180).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1180 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredSeventyTwo : IsAdmissible (evenPair 1172) :=
  isAdmissible_evenPair (by decide : Even 1172)

theorem isAdmissible_evenPair_oneThousandOneHundredSeventyFour : IsAdmissible (evenPair 1174) :=
  isAdmissible_evenPair (by decide : Even 1174)

theorem isAdmissible_evenPair_oneThousandOneHundredSeventySix : IsAdmissible (evenPair 1176) :=
  isAdmissible_evenPair (by decide : Even 1176)

theorem isAdmissible_evenPair_oneThousandOneHundredSeventyEight : IsAdmissible (evenPair 1178) :=
  isAdmissible_evenPair (by decide : Even 1178)

theorem isAdmissible_evenPair_oneThousandOneHundredEighty : IsAdmissible (evenPair 1180) :=
  isAdmissible_evenPair (by decide : Even 1180)

theorem singular_series_pos_evenPair_oneThousandOneHundredSeventyTwo : 0 < singularSeries (evenPair 1172) :=
  singular_series_pos_evenPair (by decide : Even 1172)

theorem singular_series_pos_evenPair_oneThousandOneHundredSeventyFour : 0 < singularSeries (evenPair 1174) :=
  singular_series_pos_evenPair (by decide : Even 1174)

theorem singular_series_pos_evenPair_oneThousandOneHundredSeventySix : 0 < singularSeries (evenPair 1176) :=
  singular_series_pos_evenPair (by decide : Even 1176)

theorem singular_series_pos_evenPair_oneThousandOneHundredSeventyEight : 0 < singularSeries (evenPair 1178) :=
  singular_series_pos_evenPair (by decide : Even 1178)

theorem singular_series_pos_evenPair_oneThousandOneHundredEighty : 0 < singularSeries (evenPair 1180) :=
  singular_series_pos_evenPair (by decide : Even 1180)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1172) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1172) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1174) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1174) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1176) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1176) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1178) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1178) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1180) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1180) P

theorem nu_p_oneThousandOneHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1172) p = if p = 2 ∨ p ∣ 1172 then 1 else 2 :=
  nu_p_evenPair (by decide : (1172 : ℕ) ≠ 0) (by decide : Even 1172) hp

theorem nu_p_oneThousandOneHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1174) p = if p = 2 ∨ p ∣ 1174 then 1 else 2 :=
  nu_p_evenPair (by decide : (1174 : ℕ) ≠ 0) (by decide : Even 1174) hp

theorem nu_p_oneThousandOneHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1176) p = if p = 2 ∨ p ∣ 1176 then 1 else 2 :=
  nu_p_evenPair (by decide : (1176 : ℕ) ≠ 0) (by decide : Even 1176) hp

theorem nu_p_oneThousandOneHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1178) p = if p = 2 ∨ p ∣ 1178 then 1 else 2 :=
  nu_p_evenPair (by decide : (1178 : ℕ) ≠ 0) (by decide : Even 1178) hp

theorem nu_p_oneThousandOneHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1180) p = if p = 2 ∨ p ∣ 1180 then 1 else 2 :=
  nu_p_evenPair (by decide : (1180 : ℕ) ≠ 0) (by decide : Even 1180) hp

theorem nu_p_oneThousandOneHundredSeventyTwo_two : nu_p (evenPair 1172) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1172)

theorem localFactor_oneThousandOneHundredSeventyTwo_two : localFactor (evenPair 1172) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1172 : ℕ) ≠ 0) (by decide : Even 1172)

theorem nu_p_oneThousandOneHundredEighty_two : nu_p (evenPair 1180) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1180)

theorem localFactor_oneThousandOneHundredEighty_two : localFactor (evenPair 1180) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1180 : ℕ) ≠ 0) (by decide : Even 1180)

end Brockian.SingularSeries.Gaps11721180
