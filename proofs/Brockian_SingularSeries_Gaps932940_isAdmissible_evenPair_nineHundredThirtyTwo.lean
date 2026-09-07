/-
  Brockian/SingularSeriesGaps932940.lean — even binary gaps n ∈ {932, 934, 936, 938, 940}.

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

namespace Brockian.SingularSeries.Gaps932940

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredThirtyTwo : (evenPair 932).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (932 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredThirtyFour : (evenPair 934).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (934 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredThirtySix : (evenPair 936).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (936 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredThirtyEight : (evenPair 938).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (938 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredForty : (evenPair 940).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (940 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredThirtyTwo : IsAdmissible (evenPair 932) :=
  isAdmissible_evenPair (by decide : Even 932)

theorem isAdmissible_evenPair_nineHundredThirtyFour : IsAdmissible (evenPair 934) :=
  isAdmissible_evenPair (by decide : Even 934)

theorem isAdmissible_evenPair_nineHundredThirtySix : IsAdmissible (evenPair 936) :=
  isAdmissible_evenPair (by decide : Even 936)

theorem isAdmissible_evenPair_nineHundredThirtyEight : IsAdmissible (evenPair 938) :=
  isAdmissible_evenPair (by decide : Even 938)

theorem isAdmissible_evenPair_nineHundredForty : IsAdmissible (evenPair 940) :=
  isAdmissible_evenPair (by decide : Even 940)

theorem singular_series_pos_evenPair_nineHundredThirtyTwo : 0 < singularSeries (evenPair 932) :=
  singular_series_pos_evenPair (by decide : Even 932)

theorem singular_series_pos_evenPair_nineHundredThirtyFour : 0 < singularSeries (evenPair 934) :=
  singular_series_pos_evenPair (by decide : Even 934)

theorem singular_series_pos_evenPair_nineHundredThirtySix : 0 < singularSeries (evenPair 936) :=
  singular_series_pos_evenPair (by decide : Even 936)

theorem singular_series_pos_evenPair_nineHundredThirtyEight : 0 < singularSeries (evenPair 938) :=
  singular_series_pos_evenPair (by decide : Even 938)

theorem singular_series_pos_evenPair_nineHundredForty : 0 < singularSeries (evenPair 940) :=
  singular_series_pos_evenPair (by decide : Even 940)

theorem singular_series_finite_pos_evenPair_nineHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 932) P :=
  singular_series_finite_pos_evenPair (by decide : Even 932) P

theorem singular_series_finite_pos_evenPair_nineHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 934) P :=
  singular_series_finite_pos_evenPair (by decide : Even 934) P

theorem singular_series_finite_pos_evenPair_nineHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 936) P :=
  singular_series_finite_pos_evenPair (by decide : Even 936) P

theorem singular_series_finite_pos_evenPair_nineHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 938) P :=
  singular_series_finite_pos_evenPair (by decide : Even 938) P

theorem singular_series_finite_pos_evenPair_nineHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 940) P :=
  singular_series_finite_pos_evenPair (by decide : Even 940) P

theorem nu_p_nineHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 932) p = if p = 2 ∨ p ∣ 932 then 1 else 2 :=
  nu_p_evenPair (by decide : (932 : ℕ) ≠ 0) (by decide : Even 932) hp

theorem nu_p_nineHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 934) p = if p = 2 ∨ p ∣ 934 then 1 else 2 :=
  nu_p_evenPair (by decide : (934 : ℕ) ≠ 0) (by decide : Even 934) hp

theorem nu_p_nineHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 936) p = if p = 2 ∨ p ∣ 936 then 1 else 2 :=
  nu_p_evenPair (by decide : (936 : ℕ) ≠ 0) (by decide : Even 936) hp

theorem nu_p_nineHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 938) p = if p = 2 ∨ p ∣ 938 then 1 else 2 :=
  nu_p_evenPair (by decide : (938 : ℕ) ≠ 0) (by decide : Even 938) hp

theorem nu_p_nineHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 940) p = if p = 2 ∨ p ∣ 940 then 1 else 2 :=
  nu_p_evenPair (by decide : (940 : ℕ) ≠ 0) (by decide : Even 940) hp

theorem nu_p_nineHundredThirtyTwo_two : nu_p (evenPair 932) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 932)

theorem localFactor_nineHundredThirtyTwo_two : localFactor (evenPair 932) 2 = 2 :=
  localFactor_evenPair_two (by decide : (932 : ℕ) ≠ 0) (by decide : Even 932)

theorem nu_p_nineHundredForty_two : nu_p (evenPair 940) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 940)

theorem localFactor_nineHundredForty_two : localFactor (evenPair 940) 2 = 2 :=
  localFactor_evenPair_two (by decide : (940 : ℕ) ≠ 0) (by decide : Even 940)

end Brockian.SingularSeries.Gaps932940
