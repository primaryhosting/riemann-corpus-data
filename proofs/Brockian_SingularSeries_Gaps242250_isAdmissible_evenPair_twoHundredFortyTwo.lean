/-
  Brockian/SingularSeriesGaps242250.lean — even binary gaps n ∈ {242, 244, 246, 248, 250}.

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

namespace Brockian.SingularSeries.Gaps242250

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredFortyTwo : (evenPair 242).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (242 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredFortyFour : (evenPair 244).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (244 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredFortySix : (evenPair 246).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (246 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredFortyEight : (evenPair 248).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (248 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredFifty : (evenPair 250).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (250 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredFortyTwo : IsAdmissible (evenPair 242) :=
  isAdmissible_evenPair (by decide : Even 242)

theorem isAdmissible_evenPair_twoHundredFortyFour : IsAdmissible (evenPair 244) :=
  isAdmissible_evenPair (by decide : Even 244)

theorem isAdmissible_evenPair_twoHundredFortySix : IsAdmissible (evenPair 246) :=
  isAdmissible_evenPair (by decide : Even 246)

theorem isAdmissible_evenPair_twoHundredFortyEight : IsAdmissible (evenPair 248) :=
  isAdmissible_evenPair (by decide : Even 248)

theorem isAdmissible_evenPair_twoHundredFifty : IsAdmissible (evenPair 250) :=
  isAdmissible_evenPair (by decide : Even 250)

theorem singular_series_pos_evenPair_twoHundredFortyTwo : 0 < singularSeries (evenPair 242) :=
  singular_series_pos_evenPair (by decide : Even 242)

theorem singular_series_pos_evenPair_twoHundredFortyFour : 0 < singularSeries (evenPair 244) :=
  singular_series_pos_evenPair (by decide : Even 244)

theorem singular_series_pos_evenPair_twoHundredFortySix : 0 < singularSeries (evenPair 246) :=
  singular_series_pos_evenPair (by decide : Even 246)

theorem singular_series_pos_evenPair_twoHundredFortyEight : 0 < singularSeries (evenPair 248) :=
  singular_series_pos_evenPair (by decide : Even 248)

theorem singular_series_pos_evenPair_twoHundredFifty : 0 < singularSeries (evenPair 250) :=
  singular_series_pos_evenPair (by decide : Even 250)

theorem singular_series_finite_pos_evenPair_twoHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 242) P :=
  singular_series_finite_pos_evenPair (by decide : Even 242) P

theorem singular_series_finite_pos_evenPair_twoHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 244) P :=
  singular_series_finite_pos_evenPair (by decide : Even 244) P

theorem singular_series_finite_pos_evenPair_twoHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 246) P :=
  singular_series_finite_pos_evenPair (by decide : Even 246) P

theorem singular_series_finite_pos_evenPair_twoHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 248) P :=
  singular_series_finite_pos_evenPair (by decide : Even 248) P

theorem singular_series_finite_pos_evenPair_twoHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 250) P :=
  singular_series_finite_pos_evenPair (by decide : Even 250) P

theorem nu_p_twoHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 242) p = if p = 2 ∨ p ∣ 242 then 1 else 2 :=
  nu_p_evenPair (by decide : (242 : ℕ) ≠ 0) (by decide : Even 242) hp

theorem nu_p_twoHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 244) p = if p = 2 ∨ p ∣ 244 then 1 else 2 :=
  nu_p_evenPair (by decide : (244 : ℕ) ≠ 0) (by decide : Even 244) hp

theorem nu_p_twoHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 246) p = if p = 2 ∨ p ∣ 246 then 1 else 2 :=
  nu_p_evenPair (by decide : (246 : ℕ) ≠ 0) (by decide : Even 246) hp

theorem nu_p_twoHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 248) p = if p = 2 ∨ p ∣ 248 then 1 else 2 :=
  nu_p_evenPair (by decide : (248 : ℕ) ≠ 0) (by decide : Even 248) hp

theorem nu_p_twoHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 250) p = if p = 2 ∨ p ∣ 250 then 1 else 2 :=
  nu_p_evenPair (by decide : (250 : ℕ) ≠ 0) (by decide : Even 250) hp

theorem nu_p_twoHundredFortyTwo_two : nu_p (evenPair 242) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 242)

theorem localFactor_twoHundredFortyTwo_two : localFactor (evenPair 242) 2 = 2 :=
  localFactor_evenPair_two (by decide : (242 : ℕ) ≠ 0) (by decide : Even 242)

theorem nu_p_twoHundredFifty_two : nu_p (evenPair 250) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 250)

theorem localFactor_twoHundredFifty_two : localFactor (evenPair 250) 2 = 2 :=
  localFactor_evenPair_two (by decide : (250 : ℕ) ≠ 0) (by decide : Even 250)

end Brockian.SingularSeries.Gaps242250
