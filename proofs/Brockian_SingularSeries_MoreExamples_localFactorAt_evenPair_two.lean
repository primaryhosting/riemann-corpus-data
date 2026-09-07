/-
  Brockian/SingularSeriesMoreExamples.lean — further concrete even binary gaps
  and closed local-factor data beyond SingularSeriesExamples / TwinPrimeConstant.

  Purpose: specialize the even-pair laws of `SingularSeries.Examples` to the
  concrete gaps `n ∈ {4, 6, 8, 10}`, and record clean residue counts / local
  factors for `{0,4}` and `{0,6}` in the same style as TwinPrimeConstant's
  twin-gap (`{0,2}`) closed forms.

  What is proved (all hole-free, axiom-clean over Mathlib's core):
    * `isAdmissible_evenPair_{four,six,eight,ten}`
    * `singular_series_pos_evenPair_{four,six,eight,ten}`
    * `singular_series_finite_pos_evenPair` (general even n, any bound P)
    * `evenPair_card_of_ne_zero` / card facts for 4, 6, 8, 10
    * `nu_p` closed forms for `{0,4}` and `{0,6}` (at 2 and odd primes)
    * `localFactor` / `localFactorAt` at `p = 2` for `{0,4}` and `{0,6}` (= 2)
    * small odd-prime local factors for `{0,4}` at p = 3, 5 and for `{0,6}` at p = 5

  What this is NOT:
    * Not a twin-prime / cousin-prime / sexy-prime infinitude theorem.
    * Not a Hardy–Littlewood density asymptotic.
    * Not a rewrite of SingularSeries / Wire / Examples / TwinPrimeConstant
      (import-only dependency).

  Verification (spec §2A):
    - `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}
    - AXLE independent : see registry/attestations/SingularSeriesMoreExamples.json
-/
import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesWire
import Brockian.SingularSeriesExamples

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Classical
open Real Finset
open Brockian.SingularSeries
open Brockian.SingularSeries.Wire
open Brockian.SingularSeries.Examples

namespace Brockian.SingularSeries.MoreExamples

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ## Cardinality of nonzero even pairs -/

/-- For `n ≠ 0`, the binary set `{0, n}` has cardinality exactly `2`. -/
theorem evenPair_card_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (evenPair n).card = 2 := by
  unfold evenPair
  exact card_pair (Ne.symm hn)

theorem evenPair_card_four : (evenPair 4).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (4 : ℕ) ≠ 0)

theorem evenPair_card_six : (evenPair 6).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (6 : ℕ) ≠ 0)

theorem evenPair_card_eight : (evenPair 8).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (8 : ℕ) ≠ 0)

theorem evenPair_card_ten : (evenPair 10).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (10 : ℕ) ≠ 0)

/-! ## Admissibility specializations: n ∈ {4, 6, 8, 10} -/

theorem isAdmissible_evenPair_four : IsAdmissible (evenPair 4) :=
  isAdmissible_evenPair (by decide : Even 4)

theorem isAdmissible_evenPair_six : IsAdmissible (evenPair 6) :=
  isAdmissible_evenPair (by decide : Even 6)

theorem isAdmissible_evenPair_eight : IsAdmissible (evenPair 8) :=
  isAdmissible_evenPair (by decide : Even 8)

theorem isAdmissible_evenPair_ten : IsAdmissible (evenPair 10) :=
  isAdmissible_evenPair (by decide : Even 10)

/-! ## Positive singular series: n ∈ {4, 6, 8, 10} -/

theorem singular_series_pos_evenPair_four : 0 < singularSeries (evenPair 4) :=
  singular_series_pos_evenPair (by decide : Even 4)

theorem singular_series_pos_evenPair_six : 0 < singularSeries (evenPair 6) :=
  singular_series_pos_evenPair (by decide : Even 6)

theorem singular_series_pos_evenPair_eight : 0 < singularSeries (evenPair 8) :=
  singular_series_pos_evenPair (by decide : Even 8)

theorem singular_series_pos_evenPair_ten : 0 < singularSeries (evenPair 10) :=
  singular_series_pos_evenPair (by decide : Even 10)

/-- Finite Euler products for every even binary gap stay positive. -/
theorem singular_series_finite_pos_evenPair {n : ℕ} (hn : Even n) (P : ℕ) :
    0 < singularSeriesFinite (evenPair n) P :=
  singular_series_finite_pos_of_admissible (evenPair n) P (isAdmissible_evenPair hn)

theorem singular_series_finite_pos_evenPair_four (P : ℕ) :
    0 < singularSeriesFinite (evenPair 4) P :=
  singular_series_finite_pos_evenPair (by decide : Even 4) P

theorem singular_series_finite_pos_evenPair_six (P : ℕ) :
    0 < singularSeriesFinite (evenPair 6) P :=
  singular_series_finite_pos_evenPair (by decide : Even 6) P

theorem singular_series_finite_pos_evenPair_eight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 8) P :=
  singular_series_finite_pos_evenPair (by decide : Even 8) P

theorem singular_series_finite_pos_evenPair_ten (P : ℕ) :
    0 < singularSeriesFinite (evenPair 10) P :=
  singular_series_finite_pos_evenPair (by decide : Even 10) P

/-! ## Residue counts ν_p for general even nonzero pairs -/

/-- At `p = 2`, an even gap collapses both offsets to residue `0`, so `ν₂ = 1`. -/
theorem nu_p_evenPair_two {n : ℕ} (hn : Even n) : nu_p (evenPair n) 2 = 1 := by
  have hdiv : 2 ∣ n := by rwa [even_iff_two_dvd] at hn
  have hnmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  unfold nu_p evenPair
  have himg :
      ({0, n} : Finset ℕ).image (fun x : ℕ => x % 2) = ({0} : Finset ℕ) := by
    ext y
    simp only [mem_image, mem_insert, mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · simp
      · exact hnmod
    · rintro rfl
      exact ⟨0, Or.inl rfl, by simp⟩
  rw [himg]
  simp

/-- At an odd prime not dividing `n`, residues `0` and `n` are distinct, so `ν_p = 2`
whenever `n ≠ 0`. -/
theorem nu_p_evenPair_odd_of_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p)
    (h2 : p ≠ 2) (hdiv : ¬ p ∣ n) :
    nu_p (evenPair n) p = 2 := by
  have h2lt : 2 < p := by
    have : 2 ≤ p := hp.two_le
    omega
  have hmod : n % p ≠ 0 := mt Nat.dvd_of_mod_eq_zero hdiv
  have hmod_lt : n % p < p := Nat.mod_lt n (Nat.Prime.pos hp)
  unfold nu_p evenPair
  have himg :
      ({0, n} : Finset ℕ).image (fun x : ℕ => x % p) = ({0, n % p} : Finset ℕ) := by
    ext y
    simp only [mem_image, mem_insert, mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · left; simp
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, Or.inl rfl, by simp⟩
      · exact ⟨n, Or.inr rfl, rfl⟩
  have hne : (0 : ℕ) ≠ n % p := Ne.symm hmod
  rw [himg, card_pair hne]

/-- At an odd prime dividing `n`, both offsets land on residue `0`, so `ν_p = 1`. -/
theorem nu_p_evenPair_odd_of_dvd {n p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2)
    (hdiv : p ∣ n) :
    nu_p (evenPair n) p = 1 := by
  have hnmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
  unfold nu_p evenPair
  have himg :
      ({0, n} : Finset ℕ).image (fun x : ℕ => x % p) = ({0} : Finset ℕ) := by
    ext y
    simp only [mem_image, mem_insert, mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · simp
      · exact hnmod
    · rintro rfl
      exact ⟨0, Or.inl rfl, by simp⟩
  rw [himg]
  simp

/-- Unified residue count for a nonzero even pair: `1` at `2` and at odd prime
divisors of `n`, else `2`. -/
theorem nu_p_evenPair {n p : ℕ} (hn0 : n ≠ 0) (hn : Even n) (hp : Nat.Prime p) :
    nu_p (evenPair n) p =
      if p = 2 ∨ p ∣ n then 1 else 2 := by
  split_ifs with h
  · rcases h with rfl | hdiv
    · exact nu_p_evenPair_two hn
    · by_cases h2 : p = 2
      · subst h2; exact nu_p_evenPair_two hn
      · exact nu_p_evenPair_odd_of_dvd hp h2 hdiv
  · push_neg at h
    exact nu_p_evenPair_odd_of_not_dvd hn0 hp h.1 h.2

/-! ## Closed forms: cousin primes G = {0, 4} -/

/-- `ν₂({0,4}) = 1`. -/
theorem nu_p_four_two : nu_p (evenPair 4) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 4)

/-- No odd prime divides `4`, so `ν_p({0,4}) = 2` for every odd prime. -/
theorem nu_p_four_odd {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) :
    nu_p (evenPair 4) p = 2 := by
  have hdiv : ¬ p ∣ 4 := by
    intro h
    have h4 : (4 : ℕ) = 2 * 2 := by decide
    rw [h4] at h
    have : p ∣ 2 := (Nat.Prime.dvd_mul hp).1 h |>.elim id id
    exact h2 ((Nat.dvd_prime Nat.prime_two).1 this |>.resolve_left (Nat.Prime.ne_one hp))
  exact nu_p_evenPair_odd_of_not_dvd (by decide : (4 : ℕ) ≠ 0) hp h2 hdiv

theorem nu_p_four (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 4) p = if p = 2 then 1 else 2 := by
  split_ifs with h
  · subst h; exact nu_p_four_two
  · exact nu_p_four_odd hp h

/-- Local factor of `{0,4}` at the prime `2` is exactly `2`. -/
theorem localFactor_four_two : localFactor (evenPair 4) 2 = 2 := by
  unfold localFactor
  rw [nu_p_four_two, evenPair_card_four]
  norm_num

theorem localFactorAt_four_two : localFactorAt (evenPair 4) 2 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [localFactorAt_eq, localFactor_four_two]

/-- At an odd prime, `localFactor({0,4}, p) = p(p−2)/(p−1)²`. -/
theorem localFactor_four_odd {p : ℕ} [Fact (Nat.Prime p)] (h2 : p ≠ 2) :
    localFactor (evenPair 4) p =
      (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  have hp : Nat.Prime p := Fact.out
  have hν : nu_p (evenPair 4) p = 2 := nu_p_four_odd hp h2
  have hcard : (evenPair 4).card = 2 := evenPair_card_four
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

theorem localFactorAt_four_odd {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) :
    localFactorAt (evenPair 4) p =
      (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [localFactorAt_eq, localFactor_four_odd h2]

theorem localFactor_four_three : localFactor (evenPair 4) 3 = (3 : ℝ) / 4 := by
  rw [localFactor_four_odd (by decide : (3 : ℕ) ≠ 2)]
  norm_num

theorem localFactor_four_five : localFactor (evenPair 4) 5 = (15 : ℝ) / 16 := by
  rw [localFactor_four_odd (by decide : (5 : ℕ) ≠ 2)]
  norm_num

theorem localFactorAt_four_three : localFactorAt (evenPair 4) 3 = (3 : ℝ) / 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [localFactorAt_eq, localFactor_four_three]

theorem localFactorAt_four_five : localFactorAt (evenPair 4) 5 = (15 : ℝ) / 16 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [localFactorAt_eq, localFactor_four_five]

/-! ## Closed forms: sexy primes G = {0, 6} -/

/-- `ν₂({0,6}) = 1`. -/
theorem nu_p_six_two : nu_p (evenPair 6) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 6)

/-- At `p = 3` both offsets are `0 mod 3`, so `ν₃({0,6}) = 1`. -/
theorem nu_p_six_three : nu_p (evenPair 6) 3 = 1 :=
  nu_p_evenPair_odd_of_dvd (by decide : Nat.Prime 3) (by decide : (3 : ℕ) ≠ 2)
    (by decide : 3 ∣ 6)

/-- At an odd prime other than `3`, `ν_p({0,6}) = 2`. -/
theorem nu_p_six_odd_ne_three {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    nu_p (evenPair 6) p = 2 := by
  have hdiv : ¬ p ∣ 6 := by
    intro h
    -- prime divisors of 6 are 2 and 3
    have h6 : 6 = 2 * 3 := by decide
    rw [h6] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h2' | h3'
    · exact h2 ((Nat.dvd_prime Nat.prime_two).1 h2' |>.resolve_left (Nat.Prime.ne_one hp))
    · exact h3 ((Nat.dvd_prime (by decide : Nat.Prime 3)).1 h3'
        |>.resolve_left (Nat.Prime.ne_one hp))
  exact nu_p_evenPair_odd_of_not_dvd (by decide : (6 : ℕ) ≠ 0) hp h2 hdiv

theorem nu_p_six (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 6) p =
      if p = 2 ∨ p = 3 then 1 else 2 := by
  split_ifs with h
  · rcases h with rfl | rfl
    · exact nu_p_six_two
    · exact nu_p_six_three
  · push_neg at h
    exact nu_p_six_odd_ne_three hp h.1 h.2

/-- Local factor of `{0,6}` at the prime `2` is exactly `2`. -/
theorem localFactor_six_two : localFactor (evenPair 6) 2 = 2 := by
  unfold localFactor
  rw [nu_p_six_two, evenPair_card_six]
  norm_num

theorem localFactorAt_six_two : localFactorAt (evenPair 6) 2 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [localFactorAt_eq, localFactor_six_two]

/-- At `p = 3`, `ν = 1`, so `localFactor({0,6}, 3) = (1 − 1/3)/(1 − 1/3)² = 3/2`. -/
theorem localFactor_six_three : localFactor (evenPair 6) 3 = (3 : ℝ) / 2 := by
  unfold localFactor
  rw [nu_p_six_three, evenPair_card_six]
  norm_num

theorem localFactorAt_six_three : localFactorAt (evenPair 6) 3 = (3 : ℝ) / 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [localFactorAt_eq, localFactor_six_three]

/-- At an odd prime `p ≠ 3`, `localFactor({0,6}, p) = p(p−2)/(p−1)²`. -/
theorem localFactor_six_odd_ne_three {p : ℕ} [Fact (Nat.Prime p)] (h2 : p ≠ 2)
    (h3 : p ≠ 3) :
    localFactor (evenPair 6) p =
      (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  have hp : Nat.Prime p := Fact.out
  have hν : nu_p (evenPair 6) p = 2 := nu_p_six_odd_ne_three hp h2 h3
  have hcard : (evenPair 6).card = 2 := evenPair_card_six
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

theorem localFactorAt_six_odd_ne_three {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2)
    (h3 : p ≠ 3) :
    localFactorAt (evenPair 6) p =
      (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [localFactorAt_eq, localFactor_six_odd_ne_three h2 h3]

theorem localFactor_six_five : localFactor (evenPair 6) 5 = (15 : ℝ) / 16 := by
  rw [localFactor_six_odd_ne_three (by decide : (5 : ℕ) ≠ 2) (by decide : (5 : ℕ) ≠ 3)]
  norm_num

theorem localFactorAt_six_five : localFactorAt (evenPair 6) 5 = (15 : ℝ) / 16 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [localFactorAt_eq, localFactor_six_five]

/-! ## Local factor at 2 for every even nonzero pair -/

/-- For any even nonzero gap, `localFactor({0,n}, 2) = 2`. -/
theorem localFactor_evenPair_two {n : ℕ} (hn0 : n ≠ 0) (hn : Even n) :
    localFactor (evenPair n) 2 = 2 := by
  unfold localFactor
  rw [nu_p_evenPair_two hn, evenPair_card_of_ne_zero hn0]
  norm_num

theorem localFactorAt_evenPair_two {n : ℕ} (hn0 : n ≠ 0) (hn : Even n) :
    localFactorAt (evenPair n) 2 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [localFactorAt_eq, localFactor_evenPair_two hn0 hn]

theorem localFactor_eight_two : localFactor (evenPair 8) 2 = 2 :=
  localFactor_evenPair_two (by decide : (8 : ℕ) ≠ 0) (by decide : Even 8)

theorem localFactor_ten_two : localFactor (evenPair 10) 2 = 2 :=
  localFactor_evenPair_two (by decide : (10 : ℕ) ≠ 0) (by decide : Even 10)

theorem localFactorAt_eight_two : localFactorAt (evenPair 8) 2 = 2 :=
  localFactorAt_evenPair_two (by decide : (8 : ℕ) ≠ 0) (by decide : Even 8)

theorem localFactorAt_ten_two : localFactorAt (evenPair 10) 2 = 2 :=
  localFactorAt_evenPair_two (by decide : (10 : ℕ) ≠ 0) (by decide : Even 10)

end Brockian.SingularSeries.MoreExamples
