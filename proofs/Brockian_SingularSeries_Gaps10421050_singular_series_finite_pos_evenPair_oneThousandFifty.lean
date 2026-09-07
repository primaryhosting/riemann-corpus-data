/-
  Brockian/SingularSeriesGaps10421050.lean — even binary gaps n ∈ {1042, 1044, 1046, 1048, 1050}.

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

namespace Brockian.SingularSeries.Gaps10421050

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFortyTwo : (evenPair 1042).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1042 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFortyFour : (evenPair 1044).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1044 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFortySix : (evenPair 1046).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1046 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFortyEight : (evenPair 1048).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1048 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFifty : (evenPair 1050).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1050 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFortyTwo : IsAdmissible (evenPair 1042) :=
  isAdmissible_evenPair (by decide : Even 1042)

theorem isAdmissible_evenPair_oneThousandFortyFour : IsAdmissible (evenPair 1044) :=
  isAdmissible_evenPair (by decide : Even 1044)

theorem isAdmissible_evenPair_oneThousandFortySix : IsAdmissible (evenPair 1046) :=
  isAdmissible_evenPair (by decide : Even 1046)

theorem isAdmissible_evenPair_oneThousandFortyEight : IsAdmissible (evenPair 1048) :=
  isAdmissible_evenPair (by decide : Even 1048)

theorem isAdmissible_evenPair_oneThousandFifty : IsAdmissible (evenPair 1050) :=
  isAdmissible_evenPair (by decide : Even 1050)

theorem singular_series_pos_evenPair_oneThousandFortyTwo : 0 < singularSeries (evenPair 1042) :=
  singular_series_pos_evenPair (by decide : Even 1042)

theorem singular_series_pos_evenPair_oneThousandFortyFour : 0 < singularSeries (evenPair 1044) :=
  singular_series_pos_evenPair (by decide : Even 1044)

theorem singular_series_pos_evenPair_oneThousandFortySix : 0 < singularSeries (evenPair 1046) :=
  singular_series_pos_evenPair (by decide : Even 1046)

theorem singular_series_pos_evenPair_oneThousandFortyEight : 0 < singularSeries (evenPair 1048) :=
  singular_series_pos_evenPair (by decide : Even 1048)

theorem singular_series_pos_evenPair_oneThousandFifty : 0 < singularSeries (evenPair 1050) :=
  singular_series_pos_evenPair (by decide : Even 1050)

theorem singular_series_finite_pos_evenPair_oneThousandFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1042) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1042) P

theorem singular_series_finite_pos_evenPair_oneThousandFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1044) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1044) P

theorem singular_series_finite_pos_evenPair_oneThousandFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1046) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1046) P

theorem singular_series_finite_pos_evenPair_oneThousandFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1048) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1048) P

theorem singular_series_finite_pos_evenPair_oneThousandFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1050) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1050) P

theorem nu_p_oneThousandFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1042) p = if p = 2 ∨ p ∣ 1042 then 1 else 2 :=
  nu_p_evenPair (by decide : (1042 : ℕ) ≠ 0) (by decide : Even 1042) hp

theorem nu_p_oneThousandFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1044) p = if p = 2 ∨ p ∣ 1044 then 1 else 2 :=
  nu_p_evenPair (by decide : (1044 : ℕ) ≠ 0) (by decide : Even 1044) hp

theorem nu_p_oneThousandFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1046) p = if p = 2 ∨ p ∣ 1046 then 1 else 2 :=
  nu_p_evenPair (by decide : (1046 : ℕ) ≠ 0) (by decide : Even 1046) hp

theorem nu_p_oneThousandFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1048) p = if p = 2 ∨ p ∣ 1048 then 1 else 2 :=
  nu_p_evenPair (by decide : (1048 : ℕ) ≠ 0) (by decide : Even 1048) hp

theorem nu_p_oneThousandFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1050) p = if p = 2 ∨ p ∣ 1050 then 1 else 2 :=
  nu_p_evenPair (by decide : (1050 : ℕ) ≠ 0) (by decide : Even 1050) hp

theorem nu_p_oneThousandFortyTwo_two : nu_p (evenPair 1042) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1042)

theorem localFactor_oneThousandFortyTwo_two : localFactor (evenPair 1042) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1042 : ℕ) ≠ 0) (by decide : Even 1042)

theorem nu_p_oneThousandFifty_two : nu_p (evenPair 1050) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1050)

theorem localFactor_oneThousandFifty_two : localFactor (evenPair 1050) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1050 : ℕ) ≠ 0) (by decide : Even 1050)

end Brockian.SingularSeries.Gaps10421050
