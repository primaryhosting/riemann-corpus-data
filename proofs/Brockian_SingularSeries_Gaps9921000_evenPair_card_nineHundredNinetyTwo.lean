/-
  Brockian/SingularSeriesGaps9921000.lean — even binary gaps n ∈ {992, 994, 996, 998, 1000}.

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

namespace Brockian.SingularSeries.Gaps9921000

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredNinetyTwo : (evenPair 992).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (992 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredNinetyFour : (evenPair 994).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (994 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredNinetySix : (evenPair 996).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (996 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredNinetyEight : (evenPair 998).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (998 : ℕ) ≠ 0)

theorem evenPair_card_oneThousand : (evenPair 1000).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1000 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredNinetyTwo : IsAdmissible (evenPair 992) :=
  isAdmissible_evenPair (by decide : Even 992)

theorem isAdmissible_evenPair_nineHundredNinetyFour : IsAdmissible (evenPair 994) :=
  isAdmissible_evenPair (by decide : Even 994)

theorem isAdmissible_evenPair_nineHundredNinetySix : IsAdmissible (evenPair 996) :=
  isAdmissible_evenPair (by decide : Even 996)

theorem isAdmissible_evenPair_nineHundredNinetyEight : IsAdmissible (evenPair 998) :=
  isAdmissible_evenPair (by decide : Even 998)

theorem isAdmissible_evenPair_oneThousand : IsAdmissible (evenPair 1000) :=
  isAdmissible_evenPair (by decide : Even 1000)

theorem singular_series_pos_evenPair_nineHundredNinetyTwo : 0 < singularSeries (evenPair 992) :=
  singular_series_pos_evenPair (by decide : Even 992)

theorem singular_series_pos_evenPair_nineHundredNinetyFour : 0 < singularSeries (evenPair 994) :=
  singular_series_pos_evenPair (by decide : Even 994)

theorem singular_series_pos_evenPair_nineHundredNinetySix : 0 < singularSeries (evenPair 996) :=
  singular_series_pos_evenPair (by decide : Even 996)

theorem singular_series_pos_evenPair_nineHundredNinetyEight : 0 < singularSeries (evenPair 998) :=
  singular_series_pos_evenPair (by decide : Even 998)

theorem singular_series_pos_evenPair_oneThousand : 0 < singularSeries (evenPair 1000) :=
  singular_series_pos_evenPair (by decide : Even 1000)

theorem singular_series_finite_pos_evenPair_nineHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 992) P :=
  singular_series_finite_pos_evenPair (by decide : Even 992) P

theorem singular_series_finite_pos_evenPair_nineHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 994) P :=
  singular_series_finite_pos_evenPair (by decide : Even 994) P

theorem singular_series_finite_pos_evenPair_nineHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 996) P :=
  singular_series_finite_pos_evenPair (by decide : Even 996) P

theorem singular_series_finite_pos_evenPair_nineHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 998) P :=
  singular_series_finite_pos_evenPair (by decide : Even 998) P

theorem singular_series_finite_pos_evenPair_oneThousand (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1000) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1000) P

theorem nu_p_nineHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 992) p = if p = 2 ∨ p ∣ 992 then 1 else 2 :=
  nu_p_evenPair (by decide : (992 : ℕ) ≠ 0) (by decide : Even 992) hp

theorem nu_p_nineHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 994) p = if p = 2 ∨ p ∣ 994 then 1 else 2 :=
  nu_p_evenPair (by decide : (994 : ℕ) ≠ 0) (by decide : Even 994) hp

theorem nu_p_nineHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 996) p = if p = 2 ∨ p ∣ 996 then 1 else 2 :=
  nu_p_evenPair (by decide : (996 : ℕ) ≠ 0) (by decide : Even 996) hp

theorem nu_p_nineHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 998) p = if p = 2 ∨ p ∣ 998 then 1 else 2 :=
  nu_p_evenPair (by decide : (998 : ℕ) ≠ 0) (by decide : Even 998) hp

theorem nu_p_oneThousand (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1000) p = if p = 2 ∨ p ∣ 1000 then 1 else 2 :=
  nu_p_evenPair (by decide : (1000 : ℕ) ≠ 0) (by decide : Even 1000) hp

theorem nu_p_nineHundredNinetyTwo_two : nu_p (evenPair 992) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 992)

theorem localFactor_nineHundredNinetyTwo_two : localFactor (evenPair 992) 2 = 2 :=
  localFactor_evenPair_two (by decide : (992 : ℕ) ≠ 0) (by decide : Even 992)

theorem nu_p_oneThousand_two : nu_p (evenPair 1000) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1000)

theorem localFactor_oneThousand_two : localFactor (evenPair 1000) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1000 : ℕ) ≠ 0) (by decide : Even 1000)

end Brockian.SingularSeries.Gaps9921000
