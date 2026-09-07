/-
  Brockian/SingularSeriesGaps12421250.lean — even binary gaps n ∈ {1242, 1244, 1246, 1248, 1250}.

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

namespace Brockian.SingularSeries.Gaps12421250

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredFortyTwo : (evenPair 1242).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1242 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredFortyFour : (evenPair 1244).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1244 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredFortySix : (evenPair 1246).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1246 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredFortyEight : (evenPair 1248).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1248 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredFifty : (evenPair 1250).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1250 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredFortyTwo : IsAdmissible (evenPair 1242) :=
  isAdmissible_evenPair (by decide : Even 1242)

theorem isAdmissible_evenPair_oneThousandTwoHundredFortyFour : IsAdmissible (evenPair 1244) :=
  isAdmissible_evenPair (by decide : Even 1244)

theorem isAdmissible_evenPair_oneThousandTwoHundredFortySix : IsAdmissible (evenPair 1246) :=
  isAdmissible_evenPair (by decide : Even 1246)

theorem isAdmissible_evenPair_oneThousandTwoHundredFortyEight : IsAdmissible (evenPair 1248) :=
  isAdmissible_evenPair (by decide : Even 1248)

theorem isAdmissible_evenPair_oneThousandTwoHundredFifty : IsAdmissible (evenPair 1250) :=
  isAdmissible_evenPair (by decide : Even 1250)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFortyTwo : 0 < singularSeries (evenPair 1242) :=
  singular_series_pos_evenPair (by decide : Even 1242)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFortyFour : 0 < singularSeries (evenPair 1244) :=
  singular_series_pos_evenPair (by decide : Even 1244)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFortySix : 0 < singularSeries (evenPair 1246) :=
  singular_series_pos_evenPair (by decide : Even 1246)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFortyEight : 0 < singularSeries (evenPair 1248) :=
  singular_series_pos_evenPair (by decide : Even 1248)

theorem singular_series_pos_evenPair_oneThousandTwoHundredFifty : 0 < singularSeries (evenPair 1250) :=
  singular_series_pos_evenPair (by decide : Even 1250)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1242) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1242) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1244) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1244) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1246) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1246) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1248) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1248) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1250) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1250) P

theorem nu_p_oneThousandTwoHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1242) p = if p = 2 ∨ p ∣ 1242 then 1 else 2 :=
  nu_p_evenPair (by decide : (1242 : ℕ) ≠ 0) (by decide : Even 1242) hp

theorem nu_p_oneThousandTwoHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1244) p = if p = 2 ∨ p ∣ 1244 then 1 else 2 :=
  nu_p_evenPair (by decide : (1244 : ℕ) ≠ 0) (by decide : Even 1244) hp

theorem nu_p_oneThousandTwoHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1246) p = if p = 2 ∨ p ∣ 1246 then 1 else 2 :=
  nu_p_evenPair (by decide : (1246 : ℕ) ≠ 0) (by decide : Even 1246) hp

theorem nu_p_oneThousandTwoHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1248) p = if p = 2 ∨ p ∣ 1248 then 1 else 2 :=
  nu_p_evenPair (by decide : (1248 : ℕ) ≠ 0) (by decide : Even 1248) hp

theorem nu_p_oneThousandTwoHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1250) p = if p = 2 ∨ p ∣ 1250 then 1 else 2 :=
  nu_p_evenPair (by decide : (1250 : ℕ) ≠ 0) (by decide : Even 1250) hp

theorem nu_p_oneThousandTwoHundredFortyTwo_two : nu_p (evenPair 1242) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1242)

theorem localFactor_oneThousandTwoHundredFortyTwo_two : localFactor (evenPair 1242) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1242 : ℕ) ≠ 0) (by decide : Even 1242)

theorem nu_p_oneThousandTwoHundredFifty_two : nu_p (evenPair 1250) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1250)

theorem localFactor_oneThousandTwoHundredFifty_two : localFactor (evenPair 1250) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1250 : ℕ) ≠ 0) (by decide : Even 1250)

end Brockian.SingularSeries.Gaps12421250
