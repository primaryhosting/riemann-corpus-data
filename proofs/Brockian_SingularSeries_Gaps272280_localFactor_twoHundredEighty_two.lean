/-
  Brockian/SingularSeriesGaps272280.lean — even binary gaps n ∈ {272, 274, 276, 278, 280}.

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

namespace Brockian.SingularSeries.Gaps272280

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredSeventyTwo : (evenPair 272).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (272 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSeventyFour : (evenPair 274).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (274 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSeventySix : (evenPair 276).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (276 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSeventyEight : (evenPair 278).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (278 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredEighty : (evenPair 280).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (280 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredSeventyTwo : IsAdmissible (evenPair 272) :=
  isAdmissible_evenPair (by decide : Even 272)

theorem isAdmissible_evenPair_twoHundredSeventyFour : IsAdmissible (evenPair 274) :=
  isAdmissible_evenPair (by decide : Even 274)

theorem isAdmissible_evenPair_twoHundredSeventySix : IsAdmissible (evenPair 276) :=
  isAdmissible_evenPair (by decide : Even 276)

theorem isAdmissible_evenPair_twoHundredSeventyEight : IsAdmissible (evenPair 278) :=
  isAdmissible_evenPair (by decide : Even 278)

theorem isAdmissible_evenPair_twoHundredEighty : IsAdmissible (evenPair 280) :=
  isAdmissible_evenPair (by decide : Even 280)

theorem singular_series_pos_evenPair_twoHundredSeventyTwo : 0 < singularSeries (evenPair 272) :=
  singular_series_pos_evenPair (by decide : Even 272)

theorem singular_series_pos_evenPair_twoHundredSeventyFour : 0 < singularSeries (evenPair 274) :=
  singular_series_pos_evenPair (by decide : Even 274)

theorem singular_series_pos_evenPair_twoHundredSeventySix : 0 < singularSeries (evenPair 276) :=
  singular_series_pos_evenPair (by decide : Even 276)

theorem singular_series_pos_evenPair_twoHundredSeventyEight : 0 < singularSeries (evenPair 278) :=
  singular_series_pos_evenPair (by decide : Even 278)

theorem singular_series_pos_evenPair_twoHundredEighty : 0 < singularSeries (evenPair 280) :=
  singular_series_pos_evenPair (by decide : Even 280)

theorem singular_series_finite_pos_evenPair_twoHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 272) P :=
  singular_series_finite_pos_evenPair (by decide : Even 272) P

theorem singular_series_finite_pos_evenPair_twoHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 274) P :=
  singular_series_finite_pos_evenPair (by decide : Even 274) P

theorem singular_series_finite_pos_evenPair_twoHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 276) P :=
  singular_series_finite_pos_evenPair (by decide : Even 276) P

theorem singular_series_finite_pos_evenPair_twoHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 278) P :=
  singular_series_finite_pos_evenPair (by decide : Even 278) P

theorem singular_series_finite_pos_evenPair_twoHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 280) P :=
  singular_series_finite_pos_evenPair (by decide : Even 280) P

theorem nu_p_twoHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 272) p = if p = 2 ∨ p ∣ 272 then 1 else 2 :=
  nu_p_evenPair (by decide : (272 : ℕ) ≠ 0) (by decide : Even 272) hp

theorem nu_p_twoHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 274) p = if p = 2 ∨ p ∣ 274 then 1 else 2 :=
  nu_p_evenPair (by decide : (274 : ℕ) ≠ 0) (by decide : Even 274) hp

theorem nu_p_twoHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 276) p = if p = 2 ∨ p ∣ 276 then 1 else 2 :=
  nu_p_evenPair (by decide : (276 : ℕ) ≠ 0) (by decide : Even 276) hp

theorem nu_p_twoHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 278) p = if p = 2 ∨ p ∣ 278 then 1 else 2 :=
  nu_p_evenPair (by decide : (278 : ℕ) ≠ 0) (by decide : Even 278) hp

theorem nu_p_twoHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 280) p = if p = 2 ∨ p ∣ 280 then 1 else 2 :=
  nu_p_evenPair (by decide : (280 : ℕ) ≠ 0) (by decide : Even 280) hp

theorem nu_p_twoHundredSeventyTwo_two : nu_p (evenPair 272) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 272)

theorem localFactor_twoHundredSeventyTwo_two : localFactor (evenPair 272) 2 = 2 :=
  localFactor_evenPair_two (by decide : (272 : ℕ) ≠ 0) (by decide : Even 272)

theorem nu_p_twoHundredEighty_two : nu_p (evenPair 280) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 280)

theorem localFactor_twoHundredEighty_two : localFactor (evenPair 280) 2 = 2 :=
  localFactor_evenPair_two (by decide : (280 : ℕ) ≠ 0) (by decide : Even 280)

end Brockian.SingularSeries.Gaps272280
