/-
  Brockian/SingularSeriesGaps372380.lean — even binary gaps n ∈ {372, 374, 376, 378, 380}.

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

namespace Brockian.SingularSeries.Gaps372380

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredSeventyTwo : (evenPair 372).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (372 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSeventyFour : (evenPair 374).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (374 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSeventySix : (evenPair 376).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (376 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSeventyEight : (evenPair 378).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (378 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredEighty : (evenPair 380).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (380 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredSeventyTwo : IsAdmissible (evenPair 372) :=
  isAdmissible_evenPair (by decide : Even 372)

theorem isAdmissible_evenPair_threeHundredSeventyFour : IsAdmissible (evenPair 374) :=
  isAdmissible_evenPair (by decide : Even 374)

theorem isAdmissible_evenPair_threeHundredSeventySix : IsAdmissible (evenPair 376) :=
  isAdmissible_evenPair (by decide : Even 376)

theorem isAdmissible_evenPair_threeHundredSeventyEight : IsAdmissible (evenPair 378) :=
  isAdmissible_evenPair (by decide : Even 378)

theorem isAdmissible_evenPair_threeHundredEighty : IsAdmissible (evenPair 380) :=
  isAdmissible_evenPair (by decide : Even 380)

theorem singular_series_pos_evenPair_threeHundredSeventyTwo : 0 < singularSeries (evenPair 372) :=
  singular_series_pos_evenPair (by decide : Even 372)

theorem singular_series_pos_evenPair_threeHundredSeventyFour : 0 < singularSeries (evenPair 374) :=
  singular_series_pos_evenPair (by decide : Even 374)

theorem singular_series_pos_evenPair_threeHundredSeventySix : 0 < singularSeries (evenPair 376) :=
  singular_series_pos_evenPair (by decide : Even 376)

theorem singular_series_pos_evenPair_threeHundredSeventyEight : 0 < singularSeries (evenPair 378) :=
  singular_series_pos_evenPair (by decide : Even 378)

theorem singular_series_pos_evenPair_threeHundredEighty : 0 < singularSeries (evenPair 380) :=
  singular_series_pos_evenPair (by decide : Even 380)

theorem singular_series_finite_pos_evenPair_threeHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 372) P :=
  singular_series_finite_pos_evenPair (by decide : Even 372) P

theorem singular_series_finite_pos_evenPair_threeHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 374) P :=
  singular_series_finite_pos_evenPair (by decide : Even 374) P

theorem singular_series_finite_pos_evenPair_threeHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 376) P :=
  singular_series_finite_pos_evenPair (by decide : Even 376) P

theorem singular_series_finite_pos_evenPair_threeHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 378) P :=
  singular_series_finite_pos_evenPair (by decide : Even 378) P

theorem singular_series_finite_pos_evenPair_threeHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 380) P :=
  singular_series_finite_pos_evenPair (by decide : Even 380) P

theorem nu_p_threeHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 372) p = if p = 2 ∨ p ∣ 372 then 1 else 2 :=
  nu_p_evenPair (by decide : (372 : ℕ) ≠ 0) (by decide : Even 372) hp

theorem nu_p_threeHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 374) p = if p = 2 ∨ p ∣ 374 then 1 else 2 :=
  nu_p_evenPair (by decide : (374 : ℕ) ≠ 0) (by decide : Even 374) hp

theorem nu_p_threeHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 376) p = if p = 2 ∨ p ∣ 376 then 1 else 2 :=
  nu_p_evenPair (by decide : (376 : ℕ) ≠ 0) (by decide : Even 376) hp

theorem nu_p_threeHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 378) p = if p = 2 ∨ p ∣ 378 then 1 else 2 :=
  nu_p_evenPair (by decide : (378 : ℕ) ≠ 0) (by decide : Even 378) hp

theorem nu_p_threeHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 380) p = if p = 2 ∨ p ∣ 380 then 1 else 2 :=
  nu_p_evenPair (by decide : (380 : ℕ) ≠ 0) (by decide : Even 380) hp

theorem nu_p_threeHundredSeventyTwo_two : nu_p (evenPair 372) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 372)

theorem localFactor_threeHundredSeventyTwo_two : localFactor (evenPair 372) 2 = 2 :=
  localFactor_evenPair_two (by decide : (372 : ℕ) ≠ 0) (by decide : Even 372)

theorem nu_p_threeHundredEighty_two : nu_p (evenPair 380) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 380)

theorem localFactor_threeHundredEighty_two : localFactor (evenPair 380) 2 = 2 :=
  localFactor_evenPair_two (by decide : (380 : ℕ) ≠ 0) (by decide : Even 380)

end Brockian.SingularSeries.Gaps372380
