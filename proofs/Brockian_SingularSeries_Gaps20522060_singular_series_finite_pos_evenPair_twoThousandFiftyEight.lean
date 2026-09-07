/-
  Brockian/SingularSeriesGaps20522060.lean — even binary gaps n ∈ {2052, 2054, 2056, 2058, 2060}.

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

namespace Brockian.SingularSeries.Gaps20522060

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandFiftyTwo : (evenPair 2052).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2052 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandFiftyFour : (evenPair 2054).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2054 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandFiftySix : (evenPair 2056).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2056 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandFiftyEight : (evenPair 2058).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2058 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSixty : (evenPair 2060).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2060 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandFiftyTwo : IsAdmissible (evenPair 2052) :=
  isAdmissible_evenPair (by decide : Even 2052)

theorem isAdmissible_evenPair_twoThousandFiftyFour : IsAdmissible (evenPair 2054) :=
  isAdmissible_evenPair (by decide : Even 2054)

theorem isAdmissible_evenPair_twoThousandFiftySix : IsAdmissible (evenPair 2056) :=
  isAdmissible_evenPair (by decide : Even 2056)

theorem isAdmissible_evenPair_twoThousandFiftyEight : IsAdmissible (evenPair 2058) :=
  isAdmissible_evenPair (by decide : Even 2058)

theorem isAdmissible_evenPair_twoThousandSixty : IsAdmissible (evenPair 2060) :=
  isAdmissible_evenPair (by decide : Even 2060)

theorem singular_series_pos_evenPair_twoThousandFiftyTwo : 0 < singularSeries (evenPair 2052) :=
  singular_series_pos_evenPair (by decide : Even 2052)

theorem singular_series_pos_evenPair_twoThousandFiftyFour : 0 < singularSeries (evenPair 2054) :=
  singular_series_pos_evenPair (by decide : Even 2054)

theorem singular_series_pos_evenPair_twoThousandFiftySix : 0 < singularSeries (evenPair 2056) :=
  singular_series_pos_evenPair (by decide : Even 2056)

theorem singular_series_pos_evenPair_twoThousandFiftyEight : 0 < singularSeries (evenPair 2058) :=
  singular_series_pos_evenPair (by decide : Even 2058)

theorem singular_series_pos_evenPair_twoThousandSixty : 0 < singularSeries (evenPair 2060) :=
  singular_series_pos_evenPair (by decide : Even 2060)

theorem singular_series_finite_pos_evenPair_twoThousandFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2052) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2052) P

theorem singular_series_finite_pos_evenPair_twoThousandFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2054) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2054) P

theorem singular_series_finite_pos_evenPair_twoThousandFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2056) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2056) P

theorem singular_series_finite_pos_evenPair_twoThousandFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2058) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2058) P

theorem singular_series_finite_pos_evenPair_twoThousandSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2060) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2060) P

theorem nu_p_twoThousandFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2052) p = if p = 2 ∨ p ∣ 2052 then 1 else 2 :=
  nu_p_evenPair (by decide : (2052 : ℕ) ≠ 0) (by decide : Even 2052) hp

theorem nu_p_twoThousandFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2054) p = if p = 2 ∨ p ∣ 2054 then 1 else 2 :=
  nu_p_evenPair (by decide : (2054 : ℕ) ≠ 0) (by decide : Even 2054) hp

theorem nu_p_twoThousandFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2056) p = if p = 2 ∨ p ∣ 2056 then 1 else 2 :=
  nu_p_evenPair (by decide : (2056 : ℕ) ≠ 0) (by decide : Even 2056) hp

theorem nu_p_twoThousandFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2058) p = if p = 2 ∨ p ∣ 2058 then 1 else 2 :=
  nu_p_evenPair (by decide : (2058 : ℕ) ≠ 0) (by decide : Even 2058) hp

theorem nu_p_twoThousandSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2060) p = if p = 2 ∨ p ∣ 2060 then 1 else 2 :=
  nu_p_evenPair (by decide : (2060 : ℕ) ≠ 0) (by decide : Even 2060) hp

theorem nu_p_twoThousandFiftyTwo_two : nu_p (evenPair 2052) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2052)

theorem localFactor_twoThousandFiftyTwo_two : localFactor (evenPair 2052) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2052 : ℕ) ≠ 0) (by decide : Even 2052)

theorem nu_p_twoThousandSixty_two : nu_p (evenPair 2060) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2060)

theorem localFactor_twoThousandSixty_two : localFactor (evenPair 2060) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2060 : ℕ) ≠ 0) (by decide : Even 2060)

end Brockian.SingularSeries.Gaps20522060
