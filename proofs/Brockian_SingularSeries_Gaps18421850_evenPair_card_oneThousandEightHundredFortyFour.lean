/-
  Brockian/SingularSeriesGaps18421850.lean — even binary gaps n ∈ {1842, 1844, 1846, 1848, 1850}.

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

namespace Brockian.SingularSeries.Gaps18421850

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredFortyTwo : (evenPair 1842).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1842 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredFortyFour : (evenPair 1844).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1844 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredFortySix : (evenPair 1846).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1846 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredFortyEight : (evenPair 1848).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1848 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredFifty : (evenPair 1850).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1850 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredFortyTwo : IsAdmissible (evenPair 1842) :=
  isAdmissible_evenPair (by decide : Even 1842)

theorem isAdmissible_evenPair_oneThousandEightHundredFortyFour : IsAdmissible (evenPair 1844) :=
  isAdmissible_evenPair (by decide : Even 1844)

theorem isAdmissible_evenPair_oneThousandEightHundredFortySix : IsAdmissible (evenPair 1846) :=
  isAdmissible_evenPair (by decide : Even 1846)

theorem isAdmissible_evenPair_oneThousandEightHundredFortyEight : IsAdmissible (evenPair 1848) :=
  isAdmissible_evenPair (by decide : Even 1848)

theorem isAdmissible_evenPair_oneThousandEightHundredFifty : IsAdmissible (evenPair 1850) :=
  isAdmissible_evenPair (by decide : Even 1850)

theorem singular_series_pos_evenPair_oneThousandEightHundredFortyTwo : 0 < singularSeries (evenPair 1842) :=
  singular_series_pos_evenPair (by decide : Even 1842)

theorem singular_series_pos_evenPair_oneThousandEightHundredFortyFour : 0 < singularSeries (evenPair 1844) :=
  singular_series_pos_evenPair (by decide : Even 1844)

theorem singular_series_pos_evenPair_oneThousandEightHundredFortySix : 0 < singularSeries (evenPair 1846) :=
  singular_series_pos_evenPair (by decide : Even 1846)

theorem singular_series_pos_evenPair_oneThousandEightHundredFortyEight : 0 < singularSeries (evenPair 1848) :=
  singular_series_pos_evenPair (by decide : Even 1848)

theorem singular_series_pos_evenPair_oneThousandEightHundredFifty : 0 < singularSeries (evenPair 1850) :=
  singular_series_pos_evenPair (by decide : Even 1850)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1842) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1842) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1844) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1844) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1846) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1846) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1848) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1848) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1850) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1850) P

theorem nu_p_oneThousandEightHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1842) p = if p = 2 ∨ p ∣ 1842 then 1 else 2 :=
  nu_p_evenPair (by decide : (1842 : ℕ) ≠ 0) (by decide : Even 1842) hp

theorem nu_p_oneThousandEightHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1844) p = if p = 2 ∨ p ∣ 1844 then 1 else 2 :=
  nu_p_evenPair (by decide : (1844 : ℕ) ≠ 0) (by decide : Even 1844) hp

theorem nu_p_oneThousandEightHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1846) p = if p = 2 ∨ p ∣ 1846 then 1 else 2 :=
  nu_p_evenPair (by decide : (1846 : ℕ) ≠ 0) (by decide : Even 1846) hp

theorem nu_p_oneThousandEightHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1848) p = if p = 2 ∨ p ∣ 1848 then 1 else 2 :=
  nu_p_evenPair (by decide : (1848 : ℕ) ≠ 0) (by decide : Even 1848) hp

theorem nu_p_oneThousandEightHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1850) p = if p = 2 ∨ p ∣ 1850 then 1 else 2 :=
  nu_p_evenPair (by decide : (1850 : ℕ) ≠ 0) (by decide : Even 1850) hp

theorem nu_p_oneThousandEightHundredFortyTwo_two : nu_p (evenPair 1842) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1842)

theorem localFactor_oneThousandEightHundredFortyTwo_two : localFactor (evenPair 1842) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1842 : ℕ) ≠ 0) (by decide : Even 1842)

theorem nu_p_oneThousandEightHundredFifty_two : nu_p (evenPair 1850) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1850)

theorem localFactor_oneThousandEightHundredFifty_two : localFactor (evenPair 1850) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1850 : ℕ) ≠ 0) (by decide : Even 1850)

end Brockian.SingularSeries.Gaps18421850
