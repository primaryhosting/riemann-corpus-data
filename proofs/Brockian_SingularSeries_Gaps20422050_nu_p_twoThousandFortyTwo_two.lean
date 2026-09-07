/-
  Brockian/SingularSeriesGaps20422050.lean — even binary gaps n ∈ {2042, 2044, 2046, 2048, 2050}.

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

namespace Brockian.SingularSeries.Gaps20422050

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandFortyTwo : (evenPair 2042).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2042 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandFortyFour : (evenPair 2044).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2044 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandFortySix : (evenPair 2046).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2046 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandFortyEight : (evenPair 2048).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2048 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandFifty : (evenPair 2050).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2050 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandFortyTwo : IsAdmissible (evenPair 2042) :=
  isAdmissible_evenPair (by decide : Even 2042)

theorem isAdmissible_evenPair_twoThousandFortyFour : IsAdmissible (evenPair 2044) :=
  isAdmissible_evenPair (by decide : Even 2044)

theorem isAdmissible_evenPair_twoThousandFortySix : IsAdmissible (evenPair 2046) :=
  isAdmissible_evenPair (by decide : Even 2046)

theorem isAdmissible_evenPair_twoThousandFortyEight : IsAdmissible (evenPair 2048) :=
  isAdmissible_evenPair (by decide : Even 2048)

theorem isAdmissible_evenPair_twoThousandFifty : IsAdmissible (evenPair 2050) :=
  isAdmissible_evenPair (by decide : Even 2050)

theorem singular_series_pos_evenPair_twoThousandFortyTwo : 0 < singularSeries (evenPair 2042) :=
  singular_series_pos_evenPair (by decide : Even 2042)

theorem singular_series_pos_evenPair_twoThousandFortyFour : 0 < singularSeries (evenPair 2044) :=
  singular_series_pos_evenPair (by decide : Even 2044)

theorem singular_series_pos_evenPair_twoThousandFortySix : 0 < singularSeries (evenPair 2046) :=
  singular_series_pos_evenPair (by decide : Even 2046)

theorem singular_series_pos_evenPair_twoThousandFortyEight : 0 < singularSeries (evenPair 2048) :=
  singular_series_pos_evenPair (by decide : Even 2048)

theorem singular_series_pos_evenPair_twoThousandFifty : 0 < singularSeries (evenPair 2050) :=
  singular_series_pos_evenPair (by decide : Even 2050)

theorem singular_series_finite_pos_evenPair_twoThousandFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2042) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2042) P

theorem singular_series_finite_pos_evenPair_twoThousandFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2044) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2044) P

theorem singular_series_finite_pos_evenPair_twoThousandFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2046) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2046) P

theorem singular_series_finite_pos_evenPair_twoThousandFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2048) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2048) P

theorem singular_series_finite_pos_evenPair_twoThousandFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2050) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2050) P

theorem nu_p_twoThousandFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2042) p = if p = 2 ∨ p ∣ 2042 then 1 else 2 :=
  nu_p_evenPair (by decide : (2042 : ℕ) ≠ 0) (by decide : Even 2042) hp

theorem nu_p_twoThousandFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2044) p = if p = 2 ∨ p ∣ 2044 then 1 else 2 :=
  nu_p_evenPair (by decide : (2044 : ℕ) ≠ 0) (by decide : Even 2044) hp

theorem nu_p_twoThousandFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2046) p = if p = 2 ∨ p ∣ 2046 then 1 else 2 :=
  nu_p_evenPair (by decide : (2046 : ℕ) ≠ 0) (by decide : Even 2046) hp

theorem nu_p_twoThousandFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2048) p = if p = 2 ∨ p ∣ 2048 then 1 else 2 :=
  nu_p_evenPair (by decide : (2048 : ℕ) ≠ 0) (by decide : Even 2048) hp

theorem nu_p_twoThousandFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2050) p = if p = 2 ∨ p ∣ 2050 then 1 else 2 :=
  nu_p_evenPair (by decide : (2050 : ℕ) ≠ 0) (by decide : Even 2050) hp

theorem nu_p_twoThousandFortyTwo_two : nu_p (evenPair 2042) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2042)

theorem localFactor_twoThousandFortyTwo_two : localFactor (evenPair 2042) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2042 : ℕ) ≠ 0) (by decide : Even 2042)

theorem nu_p_twoThousandFifty_two : nu_p (evenPair 2050) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2050)

theorem localFactor_twoThousandFifty_two : localFactor (evenPair 2050) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2050 : ℕ) ≠ 0) (by decide : Even 2050)

end Brockian.SingularSeries.Gaps20422050
