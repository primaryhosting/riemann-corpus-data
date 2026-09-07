/-
  Brockian/SingularSeriesEvenMore.lean — further even binary gaps beyond
  SingularSeriesMoreExamples: n ∈ {12, 14, 16, 18, 20}.

  Purpose: specialize the even-pair laws of `SingularSeries.Examples` /
  `MoreExamples` to the next even gaps, record residue counts / local factors
  for `{0,12}` at small primes, and keep the same closed-form style as
  TwinPrimeConstant / MoreExamples.

  What is proved (all hole-free, axiom-clean over Mathlib's core):
    * `isAdmissible_evenPair_{twelve,fourteen,sixteen,eighteen,twenty}`
    * `singular_series_pos_evenPair_{twelve,...,twenty}`
    * `singular_series_finite_pos_evenPair_{twelve,...,twenty}`
    * card facts for 12, 14, 16, 18, 20
    * `nu_p` closed forms for `{0,12}` (at 2, 3, and other primes)
    * `localFactor` / `localFactorAt` for `{0,12}` at p = 2, 3, 5
    * `localFactor` at 2 for each of the five gaps

  What this is NOT:
    * Not a twin-prime / cousin-prime / sexy-prime / prime-gap infinitude theorem.
    * Not a Hardy–Littlewood density asymptotic.
    * Not a rewrite of SingularSeries / Wire / Examples / MoreExamples /
      TwinPrimeConstant (import-only dependency).

  Verification (spec §2A):
    - `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}
    - AXLE independent : see registry/attestations/SingularSeriesEvenMore.json
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

namespace Brockian.SingularSeries.EvenMore

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ## Cardinality of nonzero even pairs n ∈ {12, 14, 16, 18, 20} -/

theorem evenPair_card_twelve : (evenPair 12).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (12 : ℕ) ≠ 0)

theorem evenPair_card_fourteen : (evenPair 14).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (14 : ℕ) ≠ 0)

theorem evenPair_card_sixteen : (evenPair 16).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (16 : ℕ) ≠ 0)

theorem evenPair_card_eighteen : (evenPair 18).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (18 : ℕ) ≠ 0)

theorem evenPair_card_twenty : (evenPair 20).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (20 : ℕ) ≠ 0)

/-! ## Admissibility specializations: n ∈ {12, 14, 16, 18, 20} -/

theorem isAdmissible_evenPair_twelve : IsAdmissible (evenPair 12) :=
  isAdmissible_evenPair (by decide : Even 12)

theorem isAdmissible_evenPair_fourteen : IsAdmissible (evenPair 14) :=
  isAdmissible_evenPair (by decide : Even 14)

theorem isAdmissible_evenPair_sixteen : IsAdmissible (evenPair 16) :=
  isAdmissible_evenPair (by decide : Even 16)

theorem isAdmissible_evenPair_eighteen : IsAdmissible (evenPair 18) :=
  isAdmissible_evenPair (by decide : Even 18)

theorem isAdmissible_evenPair_twenty : IsAdmissible (evenPair 20) :=
  isAdmissible_evenPair (by decide : Even 20)

/-! ## Positive singular series: n ∈ {12, 14, 16, 18, 20} -/

theorem singular_series_pos_evenPair_twelve : 0 < singularSeries (evenPair 12) :=
  singular_series_pos_evenPair (by decide : Even 12)

theorem singular_series_pos_evenPair_fourteen : 0 < singularSeries (evenPair 14) :=
  singular_series_pos_evenPair (by decide : Even 14)

theorem singular_series_pos_evenPair_sixteen : 0 < singularSeries (evenPair 16) :=
  singular_series_pos_evenPair (by decide : Even 16)

theorem singular_series_pos_evenPair_eighteen : 0 < singularSeries (evenPair 18) :=
  singular_series_pos_evenPair (by decide : Even 18)

theorem singular_series_pos_evenPair_twenty : 0 < singularSeries (evenPair 20) :=
  singular_series_pos_evenPair (by decide : Even 20)

theorem singular_series_finite_pos_evenPair_twelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 12) P :=
  singular_series_finite_pos_evenPair (by decide : Even 12) P

theorem singular_series_finite_pos_evenPair_fourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 14) P :=
  singular_series_finite_pos_evenPair (by decide : Even 14) P

theorem singular_series_finite_pos_evenPair_sixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 16) P :=
  singular_series_finite_pos_evenPair (by decide : Even 16) P

theorem singular_series_finite_pos_evenPair_eighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 18) P :=
  singular_series_finite_pos_evenPair (by decide : Even 18) P

theorem singular_series_finite_pos_evenPair_twenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 20) P :=
  singular_series_finite_pos_evenPair (by decide : Even 20) P

/-! ## Residue counts ν_p for n ∈ {12, 14, 16, 18, 20} via general laws -/

theorem nu_p_twelve_two : nu_p (evenPair 12) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 12)

theorem nu_p_fourteen_two : nu_p (evenPair 14) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 14)

theorem nu_p_sixteen_two : nu_p (evenPair 16) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 16)

theorem nu_p_eighteen_two : nu_p (evenPair 18) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 18)

theorem nu_p_twenty_two : nu_p (evenPair 20) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 20)

/-- At `p = 3` both offsets of `{0,12}` are `0 mod 3`, so `ν₃ = 1`. -/
theorem nu_p_twelve_three : nu_p (evenPair 12) 3 = 1 :=
  nu_p_evenPair_odd_of_dvd (by decide : Nat.Prime 3) (by decide : (3 : ℕ) ≠ 2)
    (by decide : 3 ∣ 12)

/-- At an odd prime other than `3`, `ν_p({0,12}) = 2`. -/
theorem nu_p_twelve_odd_ne_three {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    nu_p (evenPair 12) p = 2 := by
  have hdiv : ¬ p ∣ 12 := by
    intro h
    -- prime divisors of 12 are only 2 and 3
    have h12 : 12 = 2 * 6 := by decide
    rw [h12] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h2' | h6
    · exact h2 ((Nat.dvd_prime Nat.prime_two).1 h2' |>.resolve_left (Nat.Prime.ne_one hp))
    · have h6' : 6 = 2 * 3 := by decide
      rw [h6'] at h6
      rcases (Nat.Prime.dvd_mul hp).1 h6 with h2'' | h3'
      · exact h2 ((Nat.dvd_prime Nat.prime_two).1 h2'' |>.resolve_left (Nat.Prime.ne_one hp))
      · exact h3 ((Nat.dvd_prime (by decide : Nat.Prime 3)).1 h3'
          |>.resolve_left (Nat.Prime.ne_one hp))
  exact nu_p_evenPair_odd_of_not_dvd (by decide : (12 : ℕ) ≠ 0) hp h2 hdiv

/-- Closed form: `ν_p({0,12}) = 1` at `p = 2` or `p = 3`, else `2`. -/
theorem nu_p_twelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 12) p =
      if p = 2 ∨ p = 3 then 1 else 2 := by
  split_ifs with h
  · rcases h with rfl | rfl
    · exact nu_p_twelve_two
    · exact nu_p_twelve_three
  · push_neg at h
    exact nu_p_twelve_odd_ne_three hp h.1 h.2

/-- Unified residue count specializations via the general even-pair law. -/
theorem nu_p_fourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 14) p =
      if p = 2 ∨ p ∣ 14 then 1 else 2 :=
  nu_p_evenPair (by decide : (14 : ℕ) ≠ 0) (by decide : Even 14) hp

theorem nu_p_sixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 16) p =
      if p = 2 ∨ p ∣ 16 then 1 else 2 :=
  nu_p_evenPair (by decide : (16 : ℕ) ≠ 0) (by decide : Even 16) hp

theorem nu_p_eighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 18) p =
      if p = 2 ∨ p ∣ 18 then 1 else 2 :=
  nu_p_evenPair (by decide : (18 : ℕ) ≠ 0) (by decide : Even 18) hp

theorem nu_p_twenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 20) p =
      if p = 2 ∨ p ∣ 20 then 1 else 2 :=
  nu_p_evenPair (by decide : (20 : ℕ) ≠ 0) (by decide : Even 20) hp

/-! ## Local factors for G = {0, 12} at small primes -/

/-- Local factor of `{0,12}` at the prime `2` is exactly `2`. -/
theorem localFactor_twelve_two : localFactor (evenPair 12) 2 = 2 :=
  localFactor_evenPair_two (by decide : (12 : ℕ) ≠ 0) (by decide : Even 12)

theorem localFactorAt_twelve_two : localFactorAt (evenPair 12) 2 = 2 :=
  localFactorAt_evenPair_two (by decide : (12 : ℕ) ≠ 0) (by decide : Even 12)

/-- At `p = 3`, `ν = 1`, so `localFactor({0,12}, 3) = 3/2`. -/
theorem localFactor_twelve_three : localFactor (evenPair 12) 3 = (3 : ℝ) / 2 := by
  unfold localFactor
  rw [nu_p_twelve_three, evenPair_card_twelve]
  norm_num

theorem localFactorAt_twelve_three : localFactorAt (evenPair 12) 3 = (3 : ℝ) / 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [localFactorAt_eq, localFactor_twelve_three]

/-- At an odd prime `p ≠ 3`, `localFactor({0,12}, p) = p(p−2)/(p−1)²`. -/
theorem localFactor_twelve_odd_ne_three {p : ℕ} [Fact (Nat.Prime p)] (h2 : p ≠ 2)
    (h3 : p ≠ 3) :
    localFactor (evenPair 12) p =
      (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  have hp : Nat.Prime p := Fact.out
  have hν : nu_p (evenPair 12) p = 2 := nu_p_twelve_odd_ne_three hp h2 h3
  have hcard : (evenPair 12).card = 2 := evenPair_card_twelve
  have hppos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos hp)
  have hp1 : (1 : ℕ) < p := Nat.Prime.one_lt hp
  have h1pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
    linarith
  have h1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt h1pos
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hppos
  unfold localFactor
  rw [hν, hcard]
  field_simp
  ring

theorem localFactorAt_twelve_odd_ne_three {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2)
    (h3 : p ≠ 3) :
    localFactorAt (evenPair 12) p =
      (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [localFactorAt_eq, localFactor_twelve_odd_ne_three h2 h3]

theorem localFactor_twelve_five : localFactor (evenPair 12) 5 = (15 : ℝ) / 16 := by
  rw [localFactor_twelve_odd_ne_three (by decide : (5 : ℕ) ≠ 2) (by decide : (5 : ℕ) ≠ 3)]
  norm_num

theorem localFactorAt_twelve_five : localFactorAt (evenPair 12) 5 = (15 : ℝ) / 16 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [localFactorAt_eq, localFactor_twelve_five]

/-! ## Local factor at 2 for each gap -/

theorem localFactor_fourteen_two : localFactor (evenPair 14) 2 = 2 :=
  localFactor_evenPair_two (by decide : (14 : ℕ) ≠ 0) (by decide : Even 14)

theorem localFactor_sixteen_two : localFactor (evenPair 16) 2 = 2 :=
  localFactor_evenPair_two (by decide : (16 : ℕ) ≠ 0) (by decide : Even 16)

theorem localFactor_eighteen_two : localFactor (evenPair 18) 2 = 2 :=
  localFactor_evenPair_two (by decide : (18 : ℕ) ≠ 0) (by decide : Even 18)

theorem localFactor_twenty_two : localFactor (evenPair 20) 2 = 2 :=
  localFactor_evenPair_two (by decide : (20 : ℕ) ≠ 0) (by decide : Even 20)

theorem localFactorAt_fourteen_two : localFactorAt (evenPair 14) 2 = 2 :=
  localFactorAt_evenPair_two (by decide : (14 : ℕ) ≠ 0) (by decide : Even 14)

theorem localFactorAt_sixteen_two : localFactorAt (evenPair 16) 2 = 2 :=
  localFactorAt_evenPair_two (by decide : (16 : ℕ) ≠ 0) (by decide : Even 16)

theorem localFactorAt_eighteen_two : localFactorAt (evenPair 18) 2 = 2 :=
  localFactorAt_evenPair_two (by decide : (18 : ℕ) ≠ 0) (by decide : Even 18)

theorem localFactorAt_twenty_two : localFactorAt (evenPair 20) 2 = 2 :=
  localFactorAt_evenPair_two (by decide : (20 : ℕ) ≠ 0) (by decide : Even 20)

end Brockian.SingularSeries.EvenMore
