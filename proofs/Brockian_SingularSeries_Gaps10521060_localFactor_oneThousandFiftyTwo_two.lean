/-
  Brockian/SingularSeriesGaps10521060.lean — even binary gaps n ∈ {1052, 1054, 1056, 1058, 1060}.

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

namespace Brockian.SingularSeries.Gaps10521060

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiftyTwo : (evenPair 1052).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1052 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiftyFour : (evenPair 1054).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1054 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiftySix : (evenPair 1056).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1056 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiftyEight : (evenPair 1058).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1058 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixty : (evenPair 1060).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1060 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiftyTwo : IsAdmissible (evenPair 1052) :=
  isAdmissible_evenPair (by decide : Even 1052)

theorem isAdmissible_evenPair_oneThousandFiftyFour : IsAdmissible (evenPair 1054) :=
  isAdmissible_evenPair (by decide : Even 1054)

theorem isAdmissible_evenPair_oneThousandFiftySix : IsAdmissible (evenPair 1056) :=
  isAdmissible_evenPair (by decide : Even 1056)

theorem isAdmissible_evenPair_oneThousandFiftyEight : IsAdmissible (evenPair 1058) :=
  isAdmissible_evenPair (by decide : Even 1058)

theorem isAdmissible_evenPair_oneThousandSixty : IsAdmissible (evenPair 1060) :=
  isAdmissible_evenPair (by decide : Even 1060)

theorem singular_series_pos_evenPair_oneThousandFiftyTwo : 0 < singularSeries (evenPair 1052) :=
  singular_series_pos_evenPair (by decide : Even 1052)

theorem singular_series_pos_evenPair_oneThousandFiftyFour : 0 < singularSeries (evenPair 1054) :=
  singular_series_pos_evenPair (by decide : Even 1054)

theorem singular_series_pos_evenPair_oneThousandFiftySix : 0 < singularSeries (evenPair 1056) :=
  singular_series_pos_evenPair (by decide : Even 1056)

theorem singular_series_pos_evenPair_oneThousandFiftyEight : 0 < singularSeries (evenPair 1058) :=
  singular_series_pos_evenPair (by decide : Even 1058)

theorem singular_series_pos_evenPair_oneThousandSixty : 0 < singularSeries (evenPair 1060) :=
  singular_series_pos_evenPair (by decide : Even 1060)

theorem singular_series_finite_pos_evenPair_oneThousandFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1052) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1052) P

theorem singular_series_finite_pos_evenPair_oneThousandFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1054) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1054) P

theorem singular_series_finite_pos_evenPair_oneThousandFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1056) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1056) P

theorem singular_series_finite_pos_evenPair_oneThousandFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1058) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1058) P

theorem singular_series_finite_pos_evenPair_oneThousandSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1060) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1060) P

theorem nu_p_oneThousandFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1052) p = if p = 2 ∨ p ∣ 1052 then 1 else 2 :=
  nu_p_evenPair (by decide : (1052 : ℕ) ≠ 0) (by decide : Even 1052) hp

theorem nu_p_oneThousandFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1054) p = if p = 2 ∨ p ∣ 1054 then 1 else 2 :=
  nu_p_evenPair (by decide : (1054 : ℕ) ≠ 0) (by decide : Even 1054) hp

theorem nu_p_oneThousandFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1056) p = if p = 2 ∨ p ∣ 1056 then 1 else 2 :=
  nu_p_evenPair (by decide : (1056 : ℕ) ≠ 0) (by decide : Even 1056) hp

theorem nu_p_oneThousandFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1058) p = if p = 2 ∨ p ∣ 1058 then 1 else 2 :=
  nu_p_evenPair (by decide : (1058 : ℕ) ≠ 0) (by decide : Even 1058) hp

theorem nu_p_oneThousandSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1060) p = if p = 2 ∨ p ∣ 1060 then 1 else 2 :=
  nu_p_evenPair (by decide : (1060 : ℕ) ≠ 0) (by decide : Even 1060) hp

theorem nu_p_oneThousandFiftyTwo_two : nu_p (evenPair 1052) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1052)

theorem localFactor_oneThousandFiftyTwo_two : localFactor (evenPair 1052) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1052 : ℕ) ≠ 0) (by decide : Even 1052)

theorem nu_p_oneThousandSixty_two : nu_p (evenPair 1060) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1060)

theorem localFactor_oneThousandSixty_two : localFactor (evenPair 1060) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1060 : ℕ) ≠ 0) (by decide : Even 1060)

end Brockian.SingularSeries.Gaps10521060
