/-
  Brockian/SingularSeriesGaps172180.lean — even binary gaps n ∈ {172, 174, 176, 178, 180}.

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

namespace Brockian.SingularSeries.Gaps172180

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneHundredSeventyTwo : (evenPair 172).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (172 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSeventyFour : (evenPair 174).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (174 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSeventySix : (evenPair 176).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (176 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSeventyEight : (evenPair 178).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (178 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredEighty : (evenPair 180).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (180 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredSeventyTwo : IsAdmissible (evenPair 172) :=
  isAdmissible_evenPair (by decide : Even 172)

theorem isAdmissible_evenPair_oneHundredSeventyFour : IsAdmissible (evenPair 174) :=
  isAdmissible_evenPair (by decide : Even 174)

theorem isAdmissible_evenPair_oneHundredSeventySix : IsAdmissible (evenPair 176) :=
  isAdmissible_evenPair (by decide : Even 176)

theorem isAdmissible_evenPair_oneHundredSeventyEight : IsAdmissible (evenPair 178) :=
  isAdmissible_evenPair (by decide : Even 178)

theorem isAdmissible_evenPair_oneHundredEighty : IsAdmissible (evenPair 180) :=
  isAdmissible_evenPair (by decide : Even 180)

theorem singular_series_pos_evenPair_oneHundredSeventyTwo : 0 < singularSeries (evenPair 172) :=
  singular_series_pos_evenPair (by decide : Even 172)

theorem singular_series_pos_evenPair_oneHundredSeventyFour : 0 < singularSeries (evenPair 174) :=
  singular_series_pos_evenPair (by decide : Even 174)

theorem singular_series_pos_evenPair_oneHundredSeventySix : 0 < singularSeries (evenPair 176) :=
  singular_series_pos_evenPair (by decide : Even 176)

theorem singular_series_pos_evenPair_oneHundredSeventyEight : 0 < singularSeries (evenPair 178) :=
  singular_series_pos_evenPair (by decide : Even 178)

theorem singular_series_pos_evenPair_oneHundredEighty : 0 < singularSeries (evenPair 180) :=
  singular_series_pos_evenPair (by decide : Even 180)

theorem singular_series_finite_pos_evenPair_oneHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 172) P :=
  singular_series_finite_pos_evenPair (by decide : Even 172) P

theorem singular_series_finite_pos_evenPair_oneHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 174) P :=
  singular_series_finite_pos_evenPair (by decide : Even 174) P

theorem singular_series_finite_pos_evenPair_oneHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 176) P :=
  singular_series_finite_pos_evenPair (by decide : Even 176) P

theorem singular_series_finite_pos_evenPair_oneHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 178) P :=
  singular_series_finite_pos_evenPair (by decide : Even 178) P

theorem singular_series_finite_pos_evenPair_oneHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 180) P :=
  singular_series_finite_pos_evenPair (by decide : Even 180) P

theorem nu_p_oneHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 172) p = if p = 2 ∨ p ∣ 172 then 1 else 2 :=
  nu_p_evenPair (by decide : (172 : ℕ) ≠ 0) (by decide : Even 172) hp

theorem nu_p_oneHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 174) p = if p = 2 ∨ p ∣ 174 then 1 else 2 :=
  nu_p_evenPair (by decide : (174 : ℕ) ≠ 0) (by decide : Even 174) hp

theorem nu_p_oneHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 176) p = if p = 2 ∨ p ∣ 176 then 1 else 2 :=
  nu_p_evenPair (by decide : (176 : ℕ) ≠ 0) (by decide : Even 176) hp

theorem nu_p_oneHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 178) p = if p = 2 ∨ p ∣ 178 then 1 else 2 :=
  nu_p_evenPair (by decide : (178 : ℕ) ≠ 0) (by decide : Even 178) hp

theorem nu_p_oneHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 180) p = if p = 2 ∨ p ∣ 180 then 1 else 2 :=
  nu_p_evenPair (by decide : (180 : ℕ) ≠ 0) (by decide : Even 180) hp

theorem nu_p_oneHundredSeventyTwo_two : nu_p (evenPair 172) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 172)

theorem localFactor_oneHundredSeventyTwo_two : localFactor (evenPair 172) 2 = 2 :=
  localFactor_evenPair_two (by decide : (172 : ℕ) ≠ 0) (by decide : Even 172)

theorem nu_p_oneHundredEighty_two : nu_p (evenPair 180) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 180)

theorem localFactor_oneHundredEighty_two : localFactor (evenPair 180) 2 = 2 :=
  localFactor_evenPair_two (by decide : (180 : ℕ) ≠ 0) (by decide : Even 180)

end Brockian.SingularSeries.Gaps172180
