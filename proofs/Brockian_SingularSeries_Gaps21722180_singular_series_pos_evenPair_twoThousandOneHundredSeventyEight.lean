/-
  Brockian/SingularSeriesGaps21722180.lean — even binary gaps n ∈ {2172, 2174, 2176, 2178, 2180}.

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

namespace Brockian.SingularSeries.Gaps21722180

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredSeventyTwo : (evenPair 2172).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2172 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSeventyFour : (evenPair 2174).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2174 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSeventySix : (evenPair 2176).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2176 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSeventyEight : (evenPair 2178).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2178 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredEighty : (evenPair 2180).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2180 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredSeventyTwo : IsAdmissible (evenPair 2172) :=
  isAdmissible_evenPair (by decide : Even 2172)

theorem isAdmissible_evenPair_twoThousandOneHundredSeventyFour : IsAdmissible (evenPair 2174) :=
  isAdmissible_evenPair (by decide : Even 2174)

theorem isAdmissible_evenPair_twoThousandOneHundredSeventySix : IsAdmissible (evenPair 2176) :=
  isAdmissible_evenPair (by decide : Even 2176)

theorem isAdmissible_evenPair_twoThousandOneHundredSeventyEight : IsAdmissible (evenPair 2178) :=
  isAdmissible_evenPair (by decide : Even 2178)

theorem isAdmissible_evenPair_twoThousandOneHundredEighty : IsAdmissible (evenPair 2180) :=
  isAdmissible_evenPair (by decide : Even 2180)

theorem singular_series_pos_evenPair_twoThousandOneHundredSeventyTwo : 0 < singularSeries (evenPair 2172) :=
  singular_series_pos_evenPair (by decide : Even 2172)

theorem singular_series_pos_evenPair_twoThousandOneHundredSeventyFour : 0 < singularSeries (evenPair 2174) :=
  singular_series_pos_evenPair (by decide : Even 2174)

theorem singular_series_pos_evenPair_twoThousandOneHundredSeventySix : 0 < singularSeries (evenPair 2176) :=
  singular_series_pos_evenPair (by decide : Even 2176)

theorem singular_series_pos_evenPair_twoThousandOneHundredSeventyEight : 0 < singularSeries (evenPair 2178) :=
  singular_series_pos_evenPair (by decide : Even 2178)

theorem singular_series_pos_evenPair_twoThousandOneHundredEighty : 0 < singularSeries (evenPair 2180) :=
  singular_series_pos_evenPair (by decide : Even 2180)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2172) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2172) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2174) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2174) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2176) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2176) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2178) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2178) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2180) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2180) P

theorem nu_p_twoThousandOneHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2172) p = if p = 2 ∨ p ∣ 2172 then 1 else 2 :=
  nu_p_evenPair (by decide : (2172 : ℕ) ≠ 0) (by decide : Even 2172) hp

theorem nu_p_twoThousandOneHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2174) p = if p = 2 ∨ p ∣ 2174 then 1 else 2 :=
  nu_p_evenPair (by decide : (2174 : ℕ) ≠ 0) (by decide : Even 2174) hp

theorem nu_p_twoThousandOneHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2176) p = if p = 2 ∨ p ∣ 2176 then 1 else 2 :=
  nu_p_evenPair (by decide : (2176 : ℕ) ≠ 0) (by decide : Even 2176) hp

theorem nu_p_twoThousandOneHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2178) p = if p = 2 ∨ p ∣ 2178 then 1 else 2 :=
  nu_p_evenPair (by decide : (2178 : ℕ) ≠ 0) (by decide : Even 2178) hp

theorem nu_p_twoThousandOneHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2180) p = if p = 2 ∨ p ∣ 2180 then 1 else 2 :=
  nu_p_evenPair (by decide : (2180 : ℕ) ≠ 0) (by decide : Even 2180) hp

theorem nu_p_twoThousandOneHundredSeventyTwo_two : nu_p (evenPair 2172) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2172)

theorem localFactor_twoThousandOneHundredSeventyTwo_two : localFactor (evenPair 2172) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2172 : ℕ) ≠ 0) (by decide : Even 2172)

theorem nu_p_twoThousandOneHundredEighty_two : nu_p (evenPair 2180) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2180)

theorem localFactor_twoThousandOneHundredEighty_two : localFactor (evenPair 2180) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2180 : ℕ) ≠ 0) (by decide : Even 2180)

end Brockian.SingularSeries.Gaps21722180
