/-
  Brockian/SingularSeriesGaps222230.lean — even binary gaps n ∈ {222, 224, 226, 228, 230}.

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

namespace Brockian.SingularSeries.Gaps222230

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredTwentyTwo : (evenPair 222).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (222 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredTwentyFour : (evenPair 224).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (224 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredTwentySix : (evenPair 226).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (226 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredTwentyEight : (evenPair 228).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (228 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredThirty : (evenPair 230).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (230 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredTwentyTwo : IsAdmissible (evenPair 222) :=
  isAdmissible_evenPair (by decide : Even 222)

theorem isAdmissible_evenPair_twoHundredTwentyFour : IsAdmissible (evenPair 224) :=
  isAdmissible_evenPair (by decide : Even 224)

theorem isAdmissible_evenPair_twoHundredTwentySix : IsAdmissible (evenPair 226) :=
  isAdmissible_evenPair (by decide : Even 226)

theorem isAdmissible_evenPair_twoHundredTwentyEight : IsAdmissible (evenPair 228) :=
  isAdmissible_evenPair (by decide : Even 228)

theorem isAdmissible_evenPair_twoHundredThirty : IsAdmissible (evenPair 230) :=
  isAdmissible_evenPair (by decide : Even 230)

theorem singular_series_pos_evenPair_twoHundredTwentyTwo : 0 < singularSeries (evenPair 222) :=
  singular_series_pos_evenPair (by decide : Even 222)

theorem singular_series_pos_evenPair_twoHundredTwentyFour : 0 < singularSeries (evenPair 224) :=
  singular_series_pos_evenPair (by decide : Even 224)

theorem singular_series_pos_evenPair_twoHundredTwentySix : 0 < singularSeries (evenPair 226) :=
  singular_series_pos_evenPair (by decide : Even 226)

theorem singular_series_pos_evenPair_twoHundredTwentyEight : 0 < singularSeries (evenPair 228) :=
  singular_series_pos_evenPair (by decide : Even 228)

theorem singular_series_pos_evenPair_twoHundredThirty : 0 < singularSeries (evenPair 230) :=
  singular_series_pos_evenPair (by decide : Even 230)

theorem singular_series_finite_pos_evenPair_twoHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 222) P :=
  singular_series_finite_pos_evenPair (by decide : Even 222) P

theorem singular_series_finite_pos_evenPair_twoHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 224) P :=
  singular_series_finite_pos_evenPair (by decide : Even 224) P

theorem singular_series_finite_pos_evenPair_twoHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 226) P :=
  singular_series_finite_pos_evenPair (by decide : Even 226) P

theorem singular_series_finite_pos_evenPair_twoHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 228) P :=
  singular_series_finite_pos_evenPair (by decide : Even 228) P

theorem singular_series_finite_pos_evenPair_twoHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 230) P :=
  singular_series_finite_pos_evenPair (by decide : Even 230) P

theorem nu_p_twoHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 222) p = if p = 2 ∨ p ∣ 222 then 1 else 2 :=
  nu_p_evenPair (by decide : (222 : ℕ) ≠ 0) (by decide : Even 222) hp

theorem nu_p_twoHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 224) p = if p = 2 ∨ p ∣ 224 then 1 else 2 :=
  nu_p_evenPair (by decide : (224 : ℕ) ≠ 0) (by decide : Even 224) hp

theorem nu_p_twoHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 226) p = if p = 2 ∨ p ∣ 226 then 1 else 2 :=
  nu_p_evenPair (by decide : (226 : ℕ) ≠ 0) (by decide : Even 226) hp

theorem nu_p_twoHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 228) p = if p = 2 ∨ p ∣ 228 then 1 else 2 :=
  nu_p_evenPair (by decide : (228 : ℕ) ≠ 0) (by decide : Even 228) hp

theorem nu_p_twoHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 230) p = if p = 2 ∨ p ∣ 230 then 1 else 2 :=
  nu_p_evenPair (by decide : (230 : ℕ) ≠ 0) (by decide : Even 230) hp

theorem nu_p_twoHundredTwentyTwo_two : nu_p (evenPair 222) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 222)

theorem localFactor_twoHundredTwentyTwo_two : localFactor (evenPair 222) 2 = 2 :=
  localFactor_evenPair_two (by decide : (222 : ℕ) ≠ 0) (by decide : Even 222)

theorem nu_p_twoHundredThirty_two : nu_p (evenPair 230) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 230)

theorem localFactor_twoHundredThirty_two : localFactor (evenPair 230) 2 = 2 :=
  localFactor_evenPair_two (by decide : (230 : ℕ) ≠ 0) (by decide : Even 230)

end Brockian.SingularSeries.Gaps222230
