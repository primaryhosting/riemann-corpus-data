/-
  Brockian/SingularSeriesGaps872880.lean — even binary gaps n ∈ {872, 874, 876, 878, 880}.

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

namespace Brockian.SingularSeries.Gaps872880

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredSeventyTwo : (evenPair 872).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (872 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSeventyFour : (evenPair 874).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (874 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSeventySix : (evenPair 876).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (876 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSeventyEight : (evenPair 878).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (878 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredEighty : (evenPair 880).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (880 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredSeventyTwo : IsAdmissible (evenPair 872) :=
  isAdmissible_evenPair (by decide : Even 872)

theorem isAdmissible_evenPair_eightHundredSeventyFour : IsAdmissible (evenPair 874) :=
  isAdmissible_evenPair (by decide : Even 874)

theorem isAdmissible_evenPair_eightHundredSeventySix : IsAdmissible (evenPair 876) :=
  isAdmissible_evenPair (by decide : Even 876)

theorem isAdmissible_evenPair_eightHundredSeventyEight : IsAdmissible (evenPair 878) :=
  isAdmissible_evenPair (by decide : Even 878)

theorem isAdmissible_evenPair_eightHundredEighty : IsAdmissible (evenPair 880) :=
  isAdmissible_evenPair (by decide : Even 880)

theorem singular_series_pos_evenPair_eightHundredSeventyTwo : 0 < singularSeries (evenPair 872) :=
  singular_series_pos_evenPair (by decide : Even 872)

theorem singular_series_pos_evenPair_eightHundredSeventyFour : 0 < singularSeries (evenPair 874) :=
  singular_series_pos_evenPair (by decide : Even 874)

theorem singular_series_pos_evenPair_eightHundredSeventySix : 0 < singularSeries (evenPair 876) :=
  singular_series_pos_evenPair (by decide : Even 876)

theorem singular_series_pos_evenPair_eightHundredSeventyEight : 0 < singularSeries (evenPair 878) :=
  singular_series_pos_evenPair (by decide : Even 878)

theorem singular_series_pos_evenPair_eightHundredEighty : 0 < singularSeries (evenPair 880) :=
  singular_series_pos_evenPair (by decide : Even 880)

theorem singular_series_finite_pos_evenPair_eightHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 872) P :=
  singular_series_finite_pos_evenPair (by decide : Even 872) P

theorem singular_series_finite_pos_evenPair_eightHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 874) P :=
  singular_series_finite_pos_evenPair (by decide : Even 874) P

theorem singular_series_finite_pos_evenPair_eightHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 876) P :=
  singular_series_finite_pos_evenPair (by decide : Even 876) P

theorem singular_series_finite_pos_evenPair_eightHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 878) P :=
  singular_series_finite_pos_evenPair (by decide : Even 878) P

theorem singular_series_finite_pos_evenPair_eightHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 880) P :=
  singular_series_finite_pos_evenPair (by decide : Even 880) P

theorem nu_p_eightHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 872) p = if p = 2 ∨ p ∣ 872 then 1 else 2 :=
  nu_p_evenPair (by decide : (872 : ℕ) ≠ 0) (by decide : Even 872) hp

theorem nu_p_eightHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 874) p = if p = 2 ∨ p ∣ 874 then 1 else 2 :=
  nu_p_evenPair (by decide : (874 : ℕ) ≠ 0) (by decide : Even 874) hp

theorem nu_p_eightHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 876) p = if p = 2 ∨ p ∣ 876 then 1 else 2 :=
  nu_p_evenPair (by decide : (876 : ℕ) ≠ 0) (by decide : Even 876) hp

theorem nu_p_eightHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 878) p = if p = 2 ∨ p ∣ 878 then 1 else 2 :=
  nu_p_evenPair (by decide : (878 : ℕ) ≠ 0) (by decide : Even 878) hp

theorem nu_p_eightHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 880) p = if p = 2 ∨ p ∣ 880 then 1 else 2 :=
  nu_p_evenPair (by decide : (880 : ℕ) ≠ 0) (by decide : Even 880) hp

theorem nu_p_eightHundredSeventyTwo_two : nu_p (evenPair 872) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 872)

theorem localFactor_eightHundredSeventyTwo_two : localFactor (evenPair 872) 2 = 2 :=
  localFactor_evenPair_two (by decide : (872 : ℕ) ≠ 0) (by decide : Even 872)

theorem nu_p_eightHundredEighty_two : nu_p (evenPair 880) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 880)

theorem localFactor_eightHundredEighty_two : localFactor (evenPair 880) 2 = 2 :=
  localFactor_evenPair_two (by decide : (880 : ℕ) ≠ 0) (by decide : Even 880)

end Brockian.SingularSeries.Gaps872880
