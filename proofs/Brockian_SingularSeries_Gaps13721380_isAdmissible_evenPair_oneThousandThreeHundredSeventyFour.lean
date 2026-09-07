/-
  Brockian/SingularSeriesGaps13721380.lean — even binary gaps n ∈ {1372, 1374, 1376, 1378, 1380}.

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

namespace Brockian.SingularSeries.Gaps13721380

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredSeventyTwo : (evenPair 1372).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1372 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSeventyFour : (evenPair 1374).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1374 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSeventySix : (evenPair 1376).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1376 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredSeventyEight : (evenPair 1378).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1378 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredEighty : (evenPair 1380).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1380 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredSeventyTwo : IsAdmissible (evenPair 1372) :=
  isAdmissible_evenPair (by decide : Even 1372)

theorem isAdmissible_evenPair_oneThousandThreeHundredSeventyFour : IsAdmissible (evenPair 1374) :=
  isAdmissible_evenPair (by decide : Even 1374)

theorem isAdmissible_evenPair_oneThousandThreeHundredSeventySix : IsAdmissible (evenPair 1376) :=
  isAdmissible_evenPair (by decide : Even 1376)

theorem isAdmissible_evenPair_oneThousandThreeHundredSeventyEight : IsAdmissible (evenPair 1378) :=
  isAdmissible_evenPair (by decide : Even 1378)

theorem isAdmissible_evenPair_oneThousandThreeHundredEighty : IsAdmissible (evenPair 1380) :=
  isAdmissible_evenPair (by decide : Even 1380)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSeventyTwo : 0 < singularSeries (evenPair 1372) :=
  singular_series_pos_evenPair (by decide : Even 1372)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSeventyFour : 0 < singularSeries (evenPair 1374) :=
  singular_series_pos_evenPair (by decide : Even 1374)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSeventySix : 0 < singularSeries (evenPair 1376) :=
  singular_series_pos_evenPair (by decide : Even 1376)

theorem singular_series_pos_evenPair_oneThousandThreeHundredSeventyEight : 0 < singularSeries (evenPair 1378) :=
  singular_series_pos_evenPair (by decide : Even 1378)

theorem singular_series_pos_evenPair_oneThousandThreeHundredEighty : 0 < singularSeries (evenPair 1380) :=
  singular_series_pos_evenPair (by decide : Even 1380)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1372) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1372) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1374) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1374) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1376) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1376) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1378) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1378) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1380) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1380) P

theorem nu_p_oneThousandThreeHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1372) p = if p = 2 ∨ p ∣ 1372 then 1 else 2 :=
  nu_p_evenPair (by decide : (1372 : ℕ) ≠ 0) (by decide : Even 1372) hp

theorem nu_p_oneThousandThreeHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1374) p = if p = 2 ∨ p ∣ 1374 then 1 else 2 :=
  nu_p_evenPair (by decide : (1374 : ℕ) ≠ 0) (by decide : Even 1374) hp

theorem nu_p_oneThousandThreeHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1376) p = if p = 2 ∨ p ∣ 1376 then 1 else 2 :=
  nu_p_evenPair (by decide : (1376 : ℕ) ≠ 0) (by decide : Even 1376) hp

theorem nu_p_oneThousandThreeHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1378) p = if p = 2 ∨ p ∣ 1378 then 1 else 2 :=
  nu_p_evenPair (by decide : (1378 : ℕ) ≠ 0) (by decide : Even 1378) hp

theorem nu_p_oneThousandThreeHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1380) p = if p = 2 ∨ p ∣ 1380 then 1 else 2 :=
  nu_p_evenPair (by decide : (1380 : ℕ) ≠ 0) (by decide : Even 1380) hp

theorem nu_p_oneThousandThreeHundredSeventyTwo_two : nu_p (evenPair 1372) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1372)

theorem localFactor_oneThousandThreeHundredSeventyTwo_two : localFactor (evenPair 1372) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1372 : ℕ) ≠ 0) (by decide : Even 1372)

theorem nu_p_oneThousandThreeHundredEighty_two : nu_p (evenPair 1380) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1380)

theorem localFactor_oneThousandThreeHundredEighty_two : localFactor (evenPair 1380) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1380 : ℕ) ≠ 0) (by decide : Even 1380)

end Brockian.SingularSeries.Gaps13721380
