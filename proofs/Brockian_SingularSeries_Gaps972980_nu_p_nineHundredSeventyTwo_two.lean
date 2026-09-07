/-
  Brockian/SingularSeriesGaps972980.lean — even binary gaps n ∈ {972, 974, 976, 978, 980}.

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

namespace Brockian.SingularSeries.Gaps972980

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredSeventyTwo : (evenPair 972).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (972 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSeventyFour : (evenPair 974).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (974 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSeventySix : (evenPair 976).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (976 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSeventyEight : (evenPair 978).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (978 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredEighty : (evenPair 980).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (980 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredSeventyTwo : IsAdmissible (evenPair 972) :=
  isAdmissible_evenPair (by decide : Even 972)

theorem isAdmissible_evenPair_nineHundredSeventyFour : IsAdmissible (evenPair 974) :=
  isAdmissible_evenPair (by decide : Even 974)

theorem isAdmissible_evenPair_nineHundredSeventySix : IsAdmissible (evenPair 976) :=
  isAdmissible_evenPair (by decide : Even 976)

theorem isAdmissible_evenPair_nineHundredSeventyEight : IsAdmissible (evenPair 978) :=
  isAdmissible_evenPair (by decide : Even 978)

theorem isAdmissible_evenPair_nineHundredEighty : IsAdmissible (evenPair 980) :=
  isAdmissible_evenPair (by decide : Even 980)

theorem singular_series_pos_evenPair_nineHundredSeventyTwo : 0 < singularSeries (evenPair 972) :=
  singular_series_pos_evenPair (by decide : Even 972)

theorem singular_series_pos_evenPair_nineHundredSeventyFour : 0 < singularSeries (evenPair 974) :=
  singular_series_pos_evenPair (by decide : Even 974)

theorem singular_series_pos_evenPair_nineHundredSeventySix : 0 < singularSeries (evenPair 976) :=
  singular_series_pos_evenPair (by decide : Even 976)

theorem singular_series_pos_evenPair_nineHundredSeventyEight : 0 < singularSeries (evenPair 978) :=
  singular_series_pos_evenPair (by decide : Even 978)

theorem singular_series_pos_evenPair_nineHundredEighty : 0 < singularSeries (evenPair 980) :=
  singular_series_pos_evenPair (by decide : Even 980)

theorem singular_series_finite_pos_evenPair_nineHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 972) P :=
  singular_series_finite_pos_evenPair (by decide : Even 972) P

theorem singular_series_finite_pos_evenPair_nineHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 974) P :=
  singular_series_finite_pos_evenPair (by decide : Even 974) P

theorem singular_series_finite_pos_evenPair_nineHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 976) P :=
  singular_series_finite_pos_evenPair (by decide : Even 976) P

theorem singular_series_finite_pos_evenPair_nineHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 978) P :=
  singular_series_finite_pos_evenPair (by decide : Even 978) P

theorem singular_series_finite_pos_evenPair_nineHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 980) P :=
  singular_series_finite_pos_evenPair (by decide : Even 980) P

theorem nu_p_nineHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 972) p = if p = 2 ∨ p ∣ 972 then 1 else 2 :=
  nu_p_evenPair (by decide : (972 : ℕ) ≠ 0) (by decide : Even 972) hp

theorem nu_p_nineHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 974) p = if p = 2 ∨ p ∣ 974 then 1 else 2 :=
  nu_p_evenPair (by decide : (974 : ℕ) ≠ 0) (by decide : Even 974) hp

theorem nu_p_nineHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 976) p = if p = 2 ∨ p ∣ 976 then 1 else 2 :=
  nu_p_evenPair (by decide : (976 : ℕ) ≠ 0) (by decide : Even 976) hp

theorem nu_p_nineHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 978) p = if p = 2 ∨ p ∣ 978 then 1 else 2 :=
  nu_p_evenPair (by decide : (978 : ℕ) ≠ 0) (by decide : Even 978) hp

theorem nu_p_nineHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 980) p = if p = 2 ∨ p ∣ 980 then 1 else 2 :=
  nu_p_evenPair (by decide : (980 : ℕ) ≠ 0) (by decide : Even 980) hp

theorem nu_p_nineHundredSeventyTwo_two : nu_p (evenPair 972) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 972)

theorem localFactor_nineHundredSeventyTwo_two : localFactor (evenPair 972) 2 = 2 :=
  localFactor_evenPair_two (by decide : (972 : ℕ) ≠ 0) (by decide : Even 972)

theorem nu_p_nineHundredEighty_two : nu_p (evenPair 980) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 980)

theorem localFactor_nineHundredEighty_two : localFactor (evenPair 980) 2 = 2 :=
  localFactor_evenPair_two (by decide : (980 : ℕ) ≠ 0) (by decide : Even 980)

end Brockian.SingularSeries.Gaps972980
