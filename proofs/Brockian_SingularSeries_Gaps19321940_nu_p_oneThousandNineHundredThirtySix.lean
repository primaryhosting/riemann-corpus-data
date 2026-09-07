/-
  Brockian/SingularSeriesGaps19321940.lean — even binary gaps n ∈ {1932, 1934, 1936, 1938, 1940}.

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

namespace Brockian.SingularSeries.Gaps19321940

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredThirtyTwo : (evenPair 1932).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1932 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredThirtyFour : (evenPair 1934).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1934 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredThirtySix : (evenPair 1936).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1936 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredThirtyEight : (evenPair 1938).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1938 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredForty : (evenPair 1940).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1940 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredThirtyTwo : IsAdmissible (evenPair 1932) :=
  isAdmissible_evenPair (by decide : Even 1932)

theorem isAdmissible_evenPair_oneThousandNineHundredThirtyFour : IsAdmissible (evenPair 1934) :=
  isAdmissible_evenPair (by decide : Even 1934)

theorem isAdmissible_evenPair_oneThousandNineHundredThirtySix : IsAdmissible (evenPair 1936) :=
  isAdmissible_evenPair (by decide : Even 1936)

theorem isAdmissible_evenPair_oneThousandNineHundredThirtyEight : IsAdmissible (evenPair 1938) :=
  isAdmissible_evenPair (by decide : Even 1938)

theorem isAdmissible_evenPair_oneThousandNineHundredForty : IsAdmissible (evenPair 1940) :=
  isAdmissible_evenPair (by decide : Even 1940)

theorem singular_series_pos_evenPair_oneThousandNineHundredThirtyTwo : 0 < singularSeries (evenPair 1932) :=
  singular_series_pos_evenPair (by decide : Even 1932)

theorem singular_series_pos_evenPair_oneThousandNineHundredThirtyFour : 0 < singularSeries (evenPair 1934) :=
  singular_series_pos_evenPair (by decide : Even 1934)

theorem singular_series_pos_evenPair_oneThousandNineHundredThirtySix : 0 < singularSeries (evenPair 1936) :=
  singular_series_pos_evenPair (by decide : Even 1936)

theorem singular_series_pos_evenPair_oneThousandNineHundredThirtyEight : 0 < singularSeries (evenPair 1938) :=
  singular_series_pos_evenPair (by decide : Even 1938)

theorem singular_series_pos_evenPair_oneThousandNineHundredForty : 0 < singularSeries (evenPair 1940) :=
  singular_series_pos_evenPair (by decide : Even 1940)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1932) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1932) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1934) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1934) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1936) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1936) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1938) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1938) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1940) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1940) P

theorem nu_p_oneThousandNineHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1932) p = if p = 2 ∨ p ∣ 1932 then 1 else 2 :=
  nu_p_evenPair (by decide : (1932 : ℕ) ≠ 0) (by decide : Even 1932) hp

theorem nu_p_oneThousandNineHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1934) p = if p = 2 ∨ p ∣ 1934 then 1 else 2 :=
  nu_p_evenPair (by decide : (1934 : ℕ) ≠ 0) (by decide : Even 1934) hp

theorem nu_p_oneThousandNineHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1936) p = if p = 2 ∨ p ∣ 1936 then 1 else 2 :=
  nu_p_evenPair (by decide : (1936 : ℕ) ≠ 0) (by decide : Even 1936) hp

theorem nu_p_oneThousandNineHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1938) p = if p = 2 ∨ p ∣ 1938 then 1 else 2 :=
  nu_p_evenPair (by decide : (1938 : ℕ) ≠ 0) (by decide : Even 1938) hp

theorem nu_p_oneThousandNineHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1940) p = if p = 2 ∨ p ∣ 1940 then 1 else 2 :=
  nu_p_evenPair (by decide : (1940 : ℕ) ≠ 0) (by decide : Even 1940) hp

theorem nu_p_oneThousandNineHundredThirtyTwo_two : nu_p (evenPair 1932) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1932)

theorem localFactor_oneThousandNineHundredThirtyTwo_two : localFactor (evenPair 1932) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1932 : ℕ) ≠ 0) (by decide : Even 1932)

theorem nu_p_oneThousandNineHundredForty_two : nu_p (evenPair 1940) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1940)

theorem localFactor_oneThousandNineHundredForty_two : localFactor (evenPair 1940) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1940 : ℕ) ≠ 0) (by decide : Even 1940)

end Brockian.SingularSeries.Gaps19321940
