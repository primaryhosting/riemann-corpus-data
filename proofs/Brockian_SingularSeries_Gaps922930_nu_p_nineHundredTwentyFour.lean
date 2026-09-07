/-
  Brockian/SingularSeriesGaps922930.lean — even binary gaps n ∈ {922, 924, 926, 928, 930}.

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

namespace Brockian.SingularSeries.Gaps922930

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredTwentyTwo : (evenPair 922).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (922 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredTwentyFour : (evenPair 924).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (924 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredTwentySix : (evenPair 926).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (926 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredTwentyEight : (evenPair 928).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (928 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredThirty : (evenPair 930).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (930 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredTwentyTwo : IsAdmissible (evenPair 922) :=
  isAdmissible_evenPair (by decide : Even 922)

theorem isAdmissible_evenPair_nineHundredTwentyFour : IsAdmissible (evenPair 924) :=
  isAdmissible_evenPair (by decide : Even 924)

theorem isAdmissible_evenPair_nineHundredTwentySix : IsAdmissible (evenPair 926) :=
  isAdmissible_evenPair (by decide : Even 926)

theorem isAdmissible_evenPair_nineHundredTwentyEight : IsAdmissible (evenPair 928) :=
  isAdmissible_evenPair (by decide : Even 928)

theorem isAdmissible_evenPair_nineHundredThirty : IsAdmissible (evenPair 930) :=
  isAdmissible_evenPair (by decide : Even 930)

theorem singular_series_pos_evenPair_nineHundredTwentyTwo : 0 < singularSeries (evenPair 922) :=
  singular_series_pos_evenPair (by decide : Even 922)

theorem singular_series_pos_evenPair_nineHundredTwentyFour : 0 < singularSeries (evenPair 924) :=
  singular_series_pos_evenPair (by decide : Even 924)

theorem singular_series_pos_evenPair_nineHundredTwentySix : 0 < singularSeries (evenPair 926) :=
  singular_series_pos_evenPair (by decide : Even 926)

theorem singular_series_pos_evenPair_nineHundredTwentyEight : 0 < singularSeries (evenPair 928) :=
  singular_series_pos_evenPair (by decide : Even 928)

theorem singular_series_pos_evenPair_nineHundredThirty : 0 < singularSeries (evenPair 930) :=
  singular_series_pos_evenPair (by decide : Even 930)

theorem singular_series_finite_pos_evenPair_nineHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 922) P :=
  singular_series_finite_pos_evenPair (by decide : Even 922) P

theorem singular_series_finite_pos_evenPair_nineHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 924) P :=
  singular_series_finite_pos_evenPair (by decide : Even 924) P

theorem singular_series_finite_pos_evenPair_nineHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 926) P :=
  singular_series_finite_pos_evenPair (by decide : Even 926) P

theorem singular_series_finite_pos_evenPair_nineHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 928) P :=
  singular_series_finite_pos_evenPair (by decide : Even 928) P

theorem singular_series_finite_pos_evenPair_nineHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 930) P :=
  singular_series_finite_pos_evenPair (by decide : Even 930) P

theorem nu_p_nineHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 922) p = if p = 2 ∨ p ∣ 922 then 1 else 2 :=
  nu_p_evenPair (by decide : (922 : ℕ) ≠ 0) (by decide : Even 922) hp

theorem nu_p_nineHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 924) p = if p = 2 ∨ p ∣ 924 then 1 else 2 :=
  nu_p_evenPair (by decide : (924 : ℕ) ≠ 0) (by decide : Even 924) hp

theorem nu_p_nineHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 926) p = if p = 2 ∨ p ∣ 926 then 1 else 2 :=
  nu_p_evenPair (by decide : (926 : ℕ) ≠ 0) (by decide : Even 926) hp

theorem nu_p_nineHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 928) p = if p = 2 ∨ p ∣ 928 then 1 else 2 :=
  nu_p_evenPair (by decide : (928 : ℕ) ≠ 0) (by decide : Even 928) hp

theorem nu_p_nineHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 930) p = if p = 2 ∨ p ∣ 930 then 1 else 2 :=
  nu_p_evenPair (by decide : (930 : ℕ) ≠ 0) (by decide : Even 930) hp

theorem nu_p_nineHundredTwentyTwo_two : nu_p (evenPair 922) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 922)

theorem localFactor_nineHundredTwentyTwo_two : localFactor (evenPair 922) 2 = 2 :=
  localFactor_evenPair_two (by decide : (922 : ℕ) ≠ 0) (by decide : Even 922)

theorem nu_p_nineHundredThirty_two : nu_p (evenPair 930) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 930)

theorem localFactor_nineHundredThirty_two : localFactor (evenPair 930) 2 = 2 :=
  localFactor_evenPair_two (by decide : (930 : ℕ) ≠ 0) (by decide : Even 930)

end Brockian.SingularSeries.Gaps922930
