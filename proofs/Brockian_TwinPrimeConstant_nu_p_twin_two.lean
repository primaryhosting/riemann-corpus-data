/-
  Brockian/TwinPrimeConstant.lean — concrete reduction of the twin-gap singular series
  𝔖({0,2}).

  HONEST SCOPE: this module does NOT prove that there are infinitely many twin primes,
  does not assert the Hardy–Littlewood asymptotic for π₂(x), and does not claim any
  density lower bound.  It reduces the singular-series data for the offset set G = {0,2}
  to closed local factors and a finite Euler-product form.

  Classical identities formalized here (all PROVED, hole-free):
    * ν₂({0,2}) = 1 and ν_p({0,2}) = 2 for every odd prime p.
    * Local factor at 2:  localFactor({0,2}, 2) = 2.
    * Local factor at odd p:  localFactor({0,2}, p) = p(p−2)/(p−1)² = 1 − 1/(p−1)²
      (the GoldbachLemmas `tFactor`).
    * Finite product: for every bound P ≥ 2,
        singularSeriesFinite({0,2}, P) = 2 · ∏_{3 ≤ p ≤ P} tFactor p,
      and for P < 2 the product is empty (= 1).
    * Explicit rational values at p = 2, 3, 5, 7.
    * Positivity of the twin-gap singular series and of every finite product
      (via SingularSeriesExamples / Wire).

  Imports: SingularSeries, SingularSeriesExamples, SingularSeriesWire, GoldbachLemmas.

  Verification: AXLE `check` @ lean-4.32.0; #print axioms ⊆
  {propext, Classical.choice, Quot.sound}. No sorry / admit / axiom / native_decide.
-/
import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesWire
import Brockian.SingularSeriesExamples
import Brockian.GoldbachLemmas

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Classical
open Real Finset
open Brockian.SingularSeries
open Brockian.SingularSeries.Wire
open Brockian.SingularSeries.Examples
open Brockian.GoldbachLemmas

namespace Brockian.TwinPrimeConstant

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ## Twin-gap offset set -/

/-- Twin-gap constellation `{0, 2}` (re-export of `SingularSeries.Examples.twinGap`). -/
abbrev twinOffsets : Finset ℕ := twinGap

theorem twinOffsets_eq : twinOffsets = ({0, 2} : Finset ℕ) := twinGap_eq

theorem twinOffsets_card : twinOffsets.card = 2 := by
  simp [twinOffsets, twinGap, evenPair]

/-! ## Residue counts ν_p({0,2}) -/

/-- At `p = 2` both offsets are even, so there is a single residue class: `ν₂ = 1`. -/
theorem nu_p_twin_two : nu_p twinOffsets 2 = 1 := by
  unfold nu_p twinOffsets twinGap evenPair
  have himg :
      ({0, 2} : Finset ℕ).image (fun x : ℕ => x % 2) = ({0} : Finset ℕ) := by
    ext y
    simp only [mem_image, mem_insert, mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl <;> simp
    · rintro rfl
      exact ⟨0, Or.inl rfl, by simp⟩
  rw [himg]
  simp

/-- At an odd prime the residues `0` and `2` are distinct, so `ν_p = 2`. -/
theorem nu_p_twin_odd {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) :
    nu_p twinOffsets p = 2 := by
  have h2lt : 2 < p := by
    have : 2 ≤ p := hp.two_le
    omega
  have hmod : 2 % p = 2 := Nat.mod_eq_of_lt h2lt
  unfold nu_p twinOffsets twinGap evenPair
  have himg :
      ({0, 2} : Finset ℕ).image (fun x : ℕ => x % p) = ({0, 2} : Finset ℕ) := by
    ext y
    simp only [mem_image, mem_insert, mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · left; simp
      · right; exact hmod
    · rintro (rfl | rfl)
      · exact ⟨0, Or.inl rfl, by simp⟩
      · exact ⟨2, Or.inr rfl, hmod⟩
  have hne : (0 : ℕ) ≠ 2 := by decide
  rw [himg, card_pair hne]

/-- Residue count for the twin gap: `1` at `2`, else `2` at every other prime. -/
theorem nu_p_twin (p : ℕ) (hp : Nat.Prime p) :
    nu_p twinOffsets p = if p = 2 then 1 else 2 := by
  split_ifs with h
  · subst h; exact nu_p_twin_two
  · exact nu_p_twin_odd hp h

/-! ## Closed-form local factors -/

/-- Local factor of the twin gap at the prime `2` is exactly `2`. -/
theorem localFactor_twin_two : localFactor twinOffsets 2 = 2 := by
  unfold localFactor
  rw [nu_p_twin_two, twinOffsets_card]
  norm_num

/-- Instance-free form: `localFactorAt({0,2}, 2) = 2`. -/
theorem localFactorAt_twin_two : localFactorAt twinOffsets 2 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [localFactorAt_eq, localFactor_twin_two]

/-- At an odd prime `p ≥ 3`,
`localFactor({0,2}, p) = p(p−2)/(p−1)²`. -/
theorem localFactor_twin_odd {p : ℕ} [Fact (Nat.Prime p)] (h2 : p ≠ 2) :
    localFactor twinOffsets p =
      (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  have hp : Nat.Prime p := Fact.out
  have hp3 : 3 ≤ p := three_le_of_prime_ne_two hp h2
  have hν : nu_p twinOffsets p = 2 := nu_p_twin_odd hp h2
  have hcard : twinOffsets.card = 2 := twinOffsets_card
  have hppos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos hp)
  have h1pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  have h1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt h1pos
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hppos
  unfold localFactor
  rw [hν, hcard]
  field_simp
  ring

/-- Twin-gap local factor at an odd prime equals the generic Goldbach factor
`tFactor p = 1 − 1/(p−1)²`. -/
theorem localFactor_twin_eq_tFactor {p : ℕ} [Fact (Nat.Prime p)] (h2 : p ≠ 2) :
    localFactor twinOffsets p = tFactor p := by
  have hp : Nat.Prime p := Fact.out
  have hp3 : 3 ≤ p := three_le_of_prime_ne_two hp h2
  rw [localFactor_twin_odd h2, tFactor_eq hp3]

/-- Instance-free odd-prime form. -/
theorem localFactorAt_twin_odd {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) :
    localFactorAt twinOffsets p =
      (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [localFactorAt_eq, localFactor_twin_odd h2]

theorem localFactorAt_twin_eq_tFactor {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) :
    localFactorAt twinOffsets p = tFactor p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [localFactorAt_eq, localFactor_twin_eq_tFactor h2]

/-- Unified closed form of the twin-gap local factor at a prime. -/
theorem localFactorAt_twin (p : ℕ) (hp : Nat.Prime p) :
    localFactorAt twinOffsets p =
      if p = 2 then (2 : ℝ)
      else (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  split_ifs with h
  · subst h; exact localFactorAt_twin_two
  · exact localFactorAt_twin_odd hp h

/-! ## Explicit small-prime values -/

theorem localFactor_twin_three : localFactor twinOffsets 3 = (3 : ℝ) / 4 := by
  rw [localFactor_twin_odd (by decide : (3 : ℕ) ≠ 2)]
  norm_num

theorem localFactor_twin_five : localFactor twinOffsets 5 = (15 : ℝ) / 16 := by
  rw [localFactor_twin_odd (by decide : (5 : ℕ) ≠ 2)]
  norm_num

theorem localFactor_twin_seven : localFactor twinOffsets 7 = (35 : ℝ) / 36 := by
  rw [localFactor_twin_odd (by decide : (7 : ℕ) ≠ 2)]
  norm_num

theorem localFactorAt_twin_three : localFactorAt twinOffsets 3 = (3 : ℝ) / 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [localFactorAt_eq, localFactor_twin_three]

theorem localFactorAt_twin_five : localFactorAt twinOffsets 5 = (15 : ℝ) / 16 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [localFactorAt_eq, localFactor_twin_five]

theorem localFactorAt_twin_seven : localFactorAt twinOffsets 7 = (35 : ℝ) / 36 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [localFactorAt_eq, localFactor_twin_seven]

/-! ## Finite Euler product form -/

/-- Odd primes in the range `{0, …, P}`. -/
def oddPrimesUpTo (P : ℕ) : Finset ℕ :=
  (Finset.range (P + 1)).filter (fun p => Nat.Prime p ∧ p ≠ 2)

/-- Finite twin-prime constant product
`C₂(P) := ∏_{3 ≤ p ≤ P, p prime} (1 − 1/(p−1)²)`. -/
noncomputable def twinPrimeConstantFinite (P : ℕ) : ℝ :=
  ∏ p ∈ oddPrimesUpTo P, tFactor p

private theorem primesUpTo_eq_two_union_odd (P : ℕ) (hP : 2 ≤ P) :
    (Finset.range (P + 1)).filter Nat.Prime =
      ({2} : Finset ℕ) ∪ oddPrimesUpTo P := by
  ext p
  simp only [mem_filter, mem_range, mem_union, mem_singleton, oddPrimesUpTo]
  constructor
  · rintro ⟨hp_lt, hp⟩
    by_cases h2 : p = 2
    · exact Or.inl h2
    · exact Or.inr ⟨hp_lt, hp, h2⟩
  · rintro (rfl | ⟨hp_lt, hp, _⟩)
    · exact ⟨by omega, Nat.prime_two⟩
    · exact ⟨hp_lt, hp⟩

private theorem disjoint_two_oddPrimes (P : ℕ) :
    Disjoint ({2} : Finset ℕ) (oddPrimesUpTo P) := by
  rw [disjoint_singleton_left]
  simp [oddPrimesUpTo]

private theorem primesUpTo_empty_of_lt_two {P : ℕ} (hP : P < 2) :
    (Finset.range (P + 1)).filter Nat.Prime = (∅ : Finset ℕ) := by
  apply eq_empty_of_forall_notMem
  intro p hp
  simp only [mem_filter, mem_range] at hp
  have : 2 ≤ p := hp.2.two_le
  omega

private theorem oddPrimesUpTo_empty_of_lt_two {P : ℕ} (hP : P < 2) :
    oddPrimesUpTo P = (∅ : Finset ℕ) := by
  apply eq_empty_of_forall_notMem
  intro p hp
  simp only [oddPrimesUpTo, mem_filter, mem_range] at hp
  have : 2 ≤ p := hp.2.1.two_le
  omega

/-- The finite singular series for `{0,2}` factors as
`2 · C₂(P)` whenever the bound includes the prime `2` (i.e. `P ≥ 2`);
for `P < 2` the product is empty and equals `1`. -/
theorem singularSeriesFinite_twin_eq (P : ℕ) :
    singularSeriesFinite twinOffsets P =
      (if 2 ≤ P then (2 : ℝ) else 1) * twinPrimeConstantFinite P := by
  unfold singularSeriesFinite twinPrimeConstantFinite
  by_cases hP : 2 ≤ P
  · rw [if_pos hP, primesUpTo_eq_two_union_odd P hP,
      prod_union (disjoint_two_oddPrimes P)]
    have h2 : (∏ p ∈ ({2} : Finset ℕ), localFactorAt twinOffsets p) = (2 : ℝ) := by
      simp [localFactorAt_twin_two]
    rw [h2]
    congr 1
    apply prod_congr rfl
    intro p hp
    have hp' : Nat.Prime p ∧ p ≠ 2 := by
      simp only [oddPrimesUpTo, mem_filter, mem_range] at hp
      exact ⟨hp.2.1, hp.2.2⟩
    exact localFactorAt_twin_eq_tFactor hp'.1 hp'.2
  · push_neg at hP
    rw [if_neg (not_le.mpr hP), primesUpTo_empty_of_lt_two hP,
      oddPrimesUpTo_empty_of_lt_two hP]
    simp

/-- Specialization: for every `P ≥ 2`,
`singularSeriesFinite({0,2}, P) = 2 · twinPrimeConstantFinite P`. -/
theorem singularSeriesFinite_twin_of_two_le {P : ℕ} (hP : 2 ≤ P) :
    singularSeriesFinite twinOffsets P = 2 * twinPrimeConstantFinite P := by
  rw [singularSeriesFinite_twin_eq, if_pos hP]

/-- Finite twin-prime constant products are strictly positive. -/
theorem twinPrimeConstantFinite_pos (P : ℕ) : 0 < twinPrimeConstantFinite P := by
  unfold twinPrimeConstantFinite oddPrimesUpTo
  apply prod_pos
  intro p hp
  simp only [mem_filter, mem_range] at hp
  have hp3 : 3 ≤ p := three_le_of_prime_ne_two hp.2.1 hp.2.2
  exact tFactor_pos hp3

/-- Every twin-gap finite singular series is strictly positive. -/
theorem singularSeriesFinite_twin_pos (P : ℕ) :
    0 < singularSeriesFinite twinOffsets P :=
  singular_series_finite_pos_twinGap P

/-! ## Infinite singular series positivity (no infinitude claim) -/

/-- The twin-gap singular series is strictly positive: `0 < 𝔖({0,2})`.

This is the Hardy–Littlewood constant for the constellation `{0,2}`; it is **not**
a proof that infinitely many twin primes exist. -/
theorem singularSeries_twin_pos : 0 < singularSeries twinOffsets :=
  singular_series_pos_twinGap

/-- Twin-prime constant in the singular-series normalization `C₂' := 𝔖({0,2}) / 2`.
Classically `𝔖({0,2}) = 2 C₂` with `C₂ = ∏_{p≥3}(1 − 1/(p−1)²)`, so this is the
positive limit of `twinPrimeConstantFinite`.  Defined from the series (no separate
infinite-product construction). -/
noncomputable def twinPrimeConstant : ℝ := singularSeries twinOffsets / 2

theorem twinPrimeConstant_pos : 0 < twinPrimeConstant := by
  unfold twinPrimeConstant
  exact div_pos singularSeries_twin_pos (by norm_num)

/-- Recover the twin singular series from the twin-prime constant: `𝔖 = 2 C₂'`. -/
theorem singularSeries_twin_eq_two_mul_constant :
    singularSeries twinOffsets = 2 * twinPrimeConstant := by
  unfold twinPrimeConstant
  field_simp

/-! ## Admissibility packaging -/

theorem isAdmissible_twinOffsets : IsAdmissible twinOffsets :=
  isAdmissible_twinGap

end Brockian.TwinPrimeConstant
