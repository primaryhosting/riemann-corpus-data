/-
  Brockian/SingularSeriesGaps17821790.lean — even binary gaps n ∈ {1782, 1784, 1786, 1788, 1790}.

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

namespace Brockian.SingularSeries.Gaps17821790

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredEightyTwo : (evenPair 1782).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1782 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredEightyFour : (evenPair 1784).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1784 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredEightySix : (evenPair 1786).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1786 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredEightyEight : (evenPair 1788).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1788 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredNinety : (evenPair 1790).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1790 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredEightyTwo : IsAdmissible (evenPair 1782) :=
  isAdmissible_evenPair (by decide : Even 1782)

theorem isAdmissible_evenPair_oneThousandSevenHundredEightyFour : IsAdmissible (evenPair 1784) :=
  isAdmissible_evenPair (by decide : Even 1784)

theorem isAdmissible_evenPair_oneThousandSevenHundredEightySix : IsAdmissible (evenPair 1786) :=
  isAdmissible_evenPair (by decide : Even 1786)

theorem isAdmissible_evenPair_oneThousandSevenHundredEightyEight : IsAdmissible (evenPair 1788) :=
  isAdmissible_evenPair (by decide : Even 1788)

theorem isAdmissible_evenPair_oneThousandSevenHundredNinety : IsAdmissible (evenPair 1790) :=
  isAdmissible_evenPair (by decide : Even 1790)

theorem singular_series_pos_evenPair_oneThousandSevenHundredEightyTwo : 0 < singularSeries (evenPair 1782) :=
  singular_series_pos_evenPair (by decide : Even 1782)

theorem singular_series_pos_evenPair_oneThousandSevenHundredEightyFour : 0 < singularSeries (evenPair 1784) :=
  singular_series_pos_evenPair (by decide : Even 1784)

theorem singular_series_pos_evenPair_oneThousandSevenHundredEightySix : 0 < singularSeries (evenPair 1786) :=
  singular_series_pos_evenPair (by decide : Even 1786)

theorem singular_series_pos_evenPair_oneThousandSevenHundredEightyEight : 0 < singularSeries (evenPair 1788) :=
  singular_series_pos_evenPair (by decide : Even 1788)

theorem singular_series_pos_evenPair_oneThousandSevenHundredNinety : 0 < singularSeries (evenPair 1790) :=
  singular_series_pos_evenPair (by decide : Even 1790)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1782) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1782) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1784) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1784) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1786) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1786) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1788) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1788) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1790) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1790) P

theorem nu_p_oneThousandSevenHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1782) p = if p = 2 ∨ p ∣ 1782 then 1 else 2 :=
  nu_p_evenPair (by decide : (1782 : ℕ) ≠ 0) (by decide : Even 1782) hp

theorem nu_p_oneThousandSevenHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1784) p = if p = 2 ∨ p ∣ 1784 then 1 else 2 :=
  nu_p_evenPair (by decide : (1784 : ℕ) ≠ 0) (by decide : Even 1784) hp

theorem nu_p_oneThousandSevenHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1786) p = if p = 2 ∨ p ∣ 1786 then 1 else 2 :=
  nu_p_evenPair (by decide : (1786 : ℕ) ≠ 0) (by decide : Even 1786) hp

theorem nu_p_oneThousandSevenHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1788) p = if p = 2 ∨ p ∣ 1788 then 1 else 2 :=
  nu_p_evenPair (by decide : (1788 : ℕ) ≠ 0) (by decide : Even 1788) hp

theorem nu_p_oneThousandSevenHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1790) p = if p = 2 ∨ p ∣ 1790 then 1 else 2 :=
  nu_p_evenPair (by decide : (1790 : ℕ) ≠ 0) (by decide : Even 1790) hp

theorem nu_p_oneThousandSevenHundredEightyTwo_two : nu_p (evenPair 1782) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1782)

theorem localFactor_oneThousandSevenHundredEightyTwo_two : localFactor (evenPair 1782) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1782 : ℕ) ≠ 0) (by decide : Even 1782)

theorem nu_p_oneThousandSevenHundredNinety_two : nu_p (evenPair 1790) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1790)

theorem localFactor_oneThousandSevenHundredNinety_two : localFactor (evenPair 1790) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1790 : ℕ) ≠ 0) (by decide : Even 1790)

end Brockian.SingularSeries.Gaps17821790
