/-
  Brockian/SingularSeriesGaps19922000.lean — even binary gaps n ∈ {1992, 1994, 1996, 1998, 2000}.

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

namespace Brockian.SingularSeries.Gaps19922000

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredNinetyTwo : (evenPair 1992).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1992 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredNinetyFour : (evenPair 1994).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1994 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredNinetySix : (evenPair 1996).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1996 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredNinetyEight : (evenPair 1998).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1998 : ℕ) ≠ 0)

theorem evenPair_card_twoThousand : (evenPair 2000).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2000 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredNinetyTwo : IsAdmissible (evenPair 1992) :=
  isAdmissible_evenPair (by decide : Even 1992)

theorem isAdmissible_evenPair_oneThousandNineHundredNinetyFour : IsAdmissible (evenPair 1994) :=
  isAdmissible_evenPair (by decide : Even 1994)

theorem isAdmissible_evenPair_oneThousandNineHundredNinetySix : IsAdmissible (evenPair 1996) :=
  isAdmissible_evenPair (by decide : Even 1996)

theorem isAdmissible_evenPair_oneThousandNineHundredNinetyEight : IsAdmissible (evenPair 1998) :=
  isAdmissible_evenPair (by decide : Even 1998)

theorem isAdmissible_evenPair_twoThousand : IsAdmissible (evenPair 2000) :=
  isAdmissible_evenPair (by decide : Even 2000)

theorem singular_series_pos_evenPair_oneThousandNineHundredNinetyTwo : 0 < singularSeries (evenPair 1992) :=
  singular_series_pos_evenPair (by decide : Even 1992)

theorem singular_series_pos_evenPair_oneThousandNineHundredNinetyFour : 0 < singularSeries (evenPair 1994) :=
  singular_series_pos_evenPair (by decide : Even 1994)

theorem singular_series_pos_evenPair_oneThousandNineHundredNinetySix : 0 < singularSeries (evenPair 1996) :=
  singular_series_pos_evenPair (by decide : Even 1996)

theorem singular_series_pos_evenPair_oneThousandNineHundredNinetyEight : 0 < singularSeries (evenPair 1998) :=
  singular_series_pos_evenPair (by decide : Even 1998)

theorem singular_series_pos_evenPair_twoThousand : 0 < singularSeries (evenPair 2000) :=
  singular_series_pos_evenPair (by decide : Even 2000)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1992) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1992) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1994) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1994) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1996) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1996) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1998) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1998) P

theorem singular_series_finite_pos_evenPair_twoThousand (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2000) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2000) P

theorem nu_p_oneThousandNineHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1992) p = if p = 2 ∨ p ∣ 1992 then 1 else 2 :=
  nu_p_evenPair (by decide : (1992 : ℕ) ≠ 0) (by decide : Even 1992) hp

theorem nu_p_oneThousandNineHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1994) p = if p = 2 ∨ p ∣ 1994 then 1 else 2 :=
  nu_p_evenPair (by decide : (1994 : ℕ) ≠ 0) (by decide : Even 1994) hp

theorem nu_p_oneThousandNineHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1996) p = if p = 2 ∨ p ∣ 1996 then 1 else 2 :=
  nu_p_evenPair (by decide : (1996 : ℕ) ≠ 0) (by decide : Even 1996) hp

theorem nu_p_oneThousandNineHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1998) p = if p = 2 ∨ p ∣ 1998 then 1 else 2 :=
  nu_p_evenPair (by decide : (1998 : ℕ) ≠ 0) (by decide : Even 1998) hp

theorem nu_p_twoThousand (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2000) p = if p = 2 ∨ p ∣ 2000 then 1 else 2 :=
  nu_p_evenPair (by decide : (2000 : ℕ) ≠ 0) (by decide : Even 2000) hp

theorem nu_p_oneThousandNineHundredNinetyTwo_two : nu_p (evenPair 1992) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1992)

theorem localFactor_oneThousandNineHundredNinetyTwo_two : localFactor (evenPair 1992) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1992 : ℕ) ≠ 0) (by decide : Even 1992)

theorem nu_p_twoThousand_two : nu_p (evenPair 2000) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2000)

theorem localFactor_twoThousand_two : localFactor (evenPair 2000) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2000 : ℕ) ≠ 0) (by decide : Even 2000)

end Brockian.SingularSeries.Gaps19922000
