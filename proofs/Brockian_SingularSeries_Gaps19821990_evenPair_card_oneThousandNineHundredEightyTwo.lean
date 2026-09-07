/-
  Brockian/SingularSeriesGaps19821990.lean — even binary gaps n ∈ {1982, 1984, 1986, 1988, 1990}.

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

namespace Brockian.SingularSeries.Gaps19821990

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredEightyTwo : (evenPair 1982).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1982 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredEightyFour : (evenPair 1984).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1984 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredEightySix : (evenPair 1986).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1986 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredEightyEight : (evenPair 1988).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1988 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredNinety : (evenPair 1990).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1990 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredEightyTwo : IsAdmissible (evenPair 1982) :=
  isAdmissible_evenPair (by decide : Even 1982)

theorem isAdmissible_evenPair_oneThousandNineHundredEightyFour : IsAdmissible (evenPair 1984) :=
  isAdmissible_evenPair (by decide : Even 1984)

theorem isAdmissible_evenPair_oneThousandNineHundredEightySix : IsAdmissible (evenPair 1986) :=
  isAdmissible_evenPair (by decide : Even 1986)

theorem isAdmissible_evenPair_oneThousandNineHundredEightyEight : IsAdmissible (evenPair 1988) :=
  isAdmissible_evenPair (by decide : Even 1988)

theorem isAdmissible_evenPair_oneThousandNineHundredNinety : IsAdmissible (evenPair 1990) :=
  isAdmissible_evenPair (by decide : Even 1990)

theorem singular_series_pos_evenPair_oneThousandNineHundredEightyTwo : 0 < singularSeries (evenPair 1982) :=
  singular_series_pos_evenPair (by decide : Even 1982)

theorem singular_series_pos_evenPair_oneThousandNineHundredEightyFour : 0 < singularSeries (evenPair 1984) :=
  singular_series_pos_evenPair (by decide : Even 1984)

theorem singular_series_pos_evenPair_oneThousandNineHundredEightySix : 0 < singularSeries (evenPair 1986) :=
  singular_series_pos_evenPair (by decide : Even 1986)

theorem singular_series_pos_evenPair_oneThousandNineHundredEightyEight : 0 < singularSeries (evenPair 1988) :=
  singular_series_pos_evenPair (by decide : Even 1988)

theorem singular_series_pos_evenPair_oneThousandNineHundredNinety : 0 < singularSeries (evenPair 1990) :=
  singular_series_pos_evenPair (by decide : Even 1990)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1982) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1982) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1984) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1984) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1986) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1986) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1988) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1988) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1990) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1990) P

theorem nu_p_oneThousandNineHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1982) p = if p = 2 ∨ p ∣ 1982 then 1 else 2 :=
  nu_p_evenPair (by decide : (1982 : ℕ) ≠ 0) (by decide : Even 1982) hp

theorem nu_p_oneThousandNineHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1984) p = if p = 2 ∨ p ∣ 1984 then 1 else 2 :=
  nu_p_evenPair (by decide : (1984 : ℕ) ≠ 0) (by decide : Even 1984) hp

theorem nu_p_oneThousandNineHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1986) p = if p = 2 ∨ p ∣ 1986 then 1 else 2 :=
  nu_p_evenPair (by decide : (1986 : ℕ) ≠ 0) (by decide : Even 1986) hp

theorem nu_p_oneThousandNineHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1988) p = if p = 2 ∨ p ∣ 1988 then 1 else 2 :=
  nu_p_evenPair (by decide : (1988 : ℕ) ≠ 0) (by decide : Even 1988) hp

theorem nu_p_oneThousandNineHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1990) p = if p = 2 ∨ p ∣ 1990 then 1 else 2 :=
  nu_p_evenPair (by decide : (1990 : ℕ) ≠ 0) (by decide : Even 1990) hp

theorem nu_p_oneThousandNineHundredEightyTwo_two : nu_p (evenPair 1982) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1982)

theorem localFactor_oneThousandNineHundredEightyTwo_two : localFactor (evenPair 1982) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1982 : ℕ) ≠ 0) (by decide : Even 1982)

theorem nu_p_oneThousandNineHundredNinety_two : nu_p (evenPair 1990) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1990)

theorem localFactor_oneThousandNineHundredNinety_two : localFactor (evenPair 1990) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1990 : ℕ) ≠ 0) (by decide : Even 1990)

end Brockian.SingularSeries.Gaps19821990
