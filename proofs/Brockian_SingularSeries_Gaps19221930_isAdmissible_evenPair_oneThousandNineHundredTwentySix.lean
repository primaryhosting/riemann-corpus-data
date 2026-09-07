/-
  Brockian/SingularSeriesGaps19221930.lean — even binary gaps n ∈ {1922, 1924, 1926, 1928, 1930}.

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

namespace Brockian.SingularSeries.Gaps19221930

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredTwentyTwo : (evenPair 1922).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1922 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredTwentyFour : (evenPair 1924).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1924 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredTwentySix : (evenPair 1926).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1926 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredTwentyEight : (evenPair 1928).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1928 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredThirty : (evenPair 1930).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1930 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredTwentyTwo : IsAdmissible (evenPair 1922) :=
  isAdmissible_evenPair (by decide : Even 1922)

theorem isAdmissible_evenPair_oneThousandNineHundredTwentyFour : IsAdmissible (evenPair 1924) :=
  isAdmissible_evenPair (by decide : Even 1924)

theorem isAdmissible_evenPair_oneThousandNineHundredTwentySix : IsAdmissible (evenPair 1926) :=
  isAdmissible_evenPair (by decide : Even 1926)

theorem isAdmissible_evenPair_oneThousandNineHundredTwentyEight : IsAdmissible (evenPair 1928) :=
  isAdmissible_evenPair (by decide : Even 1928)

theorem isAdmissible_evenPair_oneThousandNineHundredThirty : IsAdmissible (evenPair 1930) :=
  isAdmissible_evenPair (by decide : Even 1930)

theorem singular_series_pos_evenPair_oneThousandNineHundredTwentyTwo : 0 < singularSeries (evenPair 1922) :=
  singular_series_pos_evenPair (by decide : Even 1922)

theorem singular_series_pos_evenPair_oneThousandNineHundredTwentyFour : 0 < singularSeries (evenPair 1924) :=
  singular_series_pos_evenPair (by decide : Even 1924)

theorem singular_series_pos_evenPair_oneThousandNineHundredTwentySix : 0 < singularSeries (evenPair 1926) :=
  singular_series_pos_evenPair (by decide : Even 1926)

theorem singular_series_pos_evenPair_oneThousandNineHundredTwentyEight : 0 < singularSeries (evenPair 1928) :=
  singular_series_pos_evenPair (by decide : Even 1928)

theorem singular_series_pos_evenPair_oneThousandNineHundredThirty : 0 < singularSeries (evenPair 1930) :=
  singular_series_pos_evenPair (by decide : Even 1930)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1922) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1922) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1924) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1924) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1926) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1926) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1928) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1928) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1930) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1930) P

theorem nu_p_oneThousandNineHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1922) p = if p = 2 ∨ p ∣ 1922 then 1 else 2 :=
  nu_p_evenPair (by decide : (1922 : ℕ) ≠ 0) (by decide : Even 1922) hp

theorem nu_p_oneThousandNineHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1924) p = if p = 2 ∨ p ∣ 1924 then 1 else 2 :=
  nu_p_evenPair (by decide : (1924 : ℕ) ≠ 0) (by decide : Even 1924) hp

theorem nu_p_oneThousandNineHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1926) p = if p = 2 ∨ p ∣ 1926 then 1 else 2 :=
  nu_p_evenPair (by decide : (1926 : ℕ) ≠ 0) (by decide : Even 1926) hp

theorem nu_p_oneThousandNineHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1928) p = if p = 2 ∨ p ∣ 1928 then 1 else 2 :=
  nu_p_evenPair (by decide : (1928 : ℕ) ≠ 0) (by decide : Even 1928) hp

theorem nu_p_oneThousandNineHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1930) p = if p = 2 ∨ p ∣ 1930 then 1 else 2 :=
  nu_p_evenPair (by decide : (1930 : ℕ) ≠ 0) (by decide : Even 1930) hp

theorem nu_p_oneThousandNineHundredTwentyTwo_two : nu_p (evenPair 1922) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1922)

theorem localFactor_oneThousandNineHundredTwentyTwo_two : localFactor (evenPair 1922) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1922 : ℕ) ≠ 0) (by decide : Even 1922)

theorem nu_p_oneThousandNineHundredThirty_two : nu_p (evenPair 1930) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1930)

theorem localFactor_oneThousandNineHundredThirty_two : localFactor (evenPair 1930) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1930 : ℕ) ≠ 0) (by decide : Even 1930)

end Brockian.SingularSeries.Gaps19221930
