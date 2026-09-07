/-
  Brockian/SingularSeriesGaps782790.lean — even binary gaps n ∈ {782, 784, 786, 788, 790}.

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

namespace Brockian.SingularSeries.Gaps782790

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredEightyTwo : (evenPair 782).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (782 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredEightyFour : (evenPair 784).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (784 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredEightySix : (evenPair 786).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (786 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredEightyEight : (evenPair 788).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (788 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredNinety : (evenPair 790).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (790 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredEightyTwo : IsAdmissible (evenPair 782) :=
  isAdmissible_evenPair (by decide : Even 782)

theorem isAdmissible_evenPair_sevenHundredEightyFour : IsAdmissible (evenPair 784) :=
  isAdmissible_evenPair (by decide : Even 784)

theorem isAdmissible_evenPair_sevenHundredEightySix : IsAdmissible (evenPair 786) :=
  isAdmissible_evenPair (by decide : Even 786)

theorem isAdmissible_evenPair_sevenHundredEightyEight : IsAdmissible (evenPair 788) :=
  isAdmissible_evenPair (by decide : Even 788)

theorem isAdmissible_evenPair_sevenHundredNinety : IsAdmissible (evenPair 790) :=
  isAdmissible_evenPair (by decide : Even 790)

theorem singular_series_pos_evenPair_sevenHundredEightyTwo : 0 < singularSeries (evenPair 782) :=
  singular_series_pos_evenPair (by decide : Even 782)

theorem singular_series_pos_evenPair_sevenHundredEightyFour : 0 < singularSeries (evenPair 784) :=
  singular_series_pos_evenPair (by decide : Even 784)

theorem singular_series_pos_evenPair_sevenHundredEightySix : 0 < singularSeries (evenPair 786) :=
  singular_series_pos_evenPair (by decide : Even 786)

theorem singular_series_pos_evenPair_sevenHundredEightyEight : 0 < singularSeries (evenPair 788) :=
  singular_series_pos_evenPair (by decide : Even 788)

theorem singular_series_pos_evenPair_sevenHundredNinety : 0 < singularSeries (evenPair 790) :=
  singular_series_pos_evenPair (by decide : Even 790)

theorem singular_series_finite_pos_evenPair_sevenHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 782) P :=
  singular_series_finite_pos_evenPair (by decide : Even 782) P

theorem singular_series_finite_pos_evenPair_sevenHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 784) P :=
  singular_series_finite_pos_evenPair (by decide : Even 784) P

theorem singular_series_finite_pos_evenPair_sevenHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 786) P :=
  singular_series_finite_pos_evenPair (by decide : Even 786) P

theorem singular_series_finite_pos_evenPair_sevenHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 788) P :=
  singular_series_finite_pos_evenPair (by decide : Even 788) P

theorem singular_series_finite_pos_evenPair_sevenHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 790) P :=
  singular_series_finite_pos_evenPair (by decide : Even 790) P

theorem nu_p_sevenHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 782) p = if p = 2 ∨ p ∣ 782 then 1 else 2 :=
  nu_p_evenPair (by decide : (782 : ℕ) ≠ 0) (by decide : Even 782) hp

theorem nu_p_sevenHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 784) p = if p = 2 ∨ p ∣ 784 then 1 else 2 :=
  nu_p_evenPair (by decide : (784 : ℕ) ≠ 0) (by decide : Even 784) hp

theorem nu_p_sevenHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 786) p = if p = 2 ∨ p ∣ 786 then 1 else 2 :=
  nu_p_evenPair (by decide : (786 : ℕ) ≠ 0) (by decide : Even 786) hp

theorem nu_p_sevenHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 788) p = if p = 2 ∨ p ∣ 788 then 1 else 2 :=
  nu_p_evenPair (by decide : (788 : ℕ) ≠ 0) (by decide : Even 788) hp

theorem nu_p_sevenHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 790) p = if p = 2 ∨ p ∣ 790 then 1 else 2 :=
  nu_p_evenPair (by decide : (790 : ℕ) ≠ 0) (by decide : Even 790) hp

theorem nu_p_sevenHundredEightyTwo_two : nu_p (evenPair 782) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 782)

theorem localFactor_sevenHundredEightyTwo_two : localFactor (evenPair 782) 2 = 2 :=
  localFactor_evenPair_two (by decide : (782 : ℕ) ≠ 0) (by decide : Even 782)

theorem nu_p_sevenHundredNinety_two : nu_p (evenPair 790) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 790)

theorem localFactor_sevenHundredNinety_two : localFactor (evenPair 790) 2 = 2 :=
  localFactor_evenPair_two (by decide : (790 : ℕ) ≠ 0) (by decide : Even 790)

end Brockian.SingularSeries.Gaps782790
