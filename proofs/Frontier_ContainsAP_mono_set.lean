import Mathlib
/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the module docstring above is placed immediately after `import Mathlib`.

## Contents

* `Frontier.ContainsAP A k` : the set `A ⊆ ℕ` contains an arithmetic progression of length `k`
  with positive common difference.
* `Frontier.upperDensity A` : the upper asymptotic density of `A ⊆ ℕ`.
* `Frontier.FinitarySzemeredi k` : the finitary form of Szemerédi's theorem for progressions of
  length `k`.
* `Frontier.furstenberg_szemeredi` : the reduction of Szemerédi's theorem (positive upper density
  sets of naturals contain arbitrarily long arithmetic progressions) to its finitary form.
* `Frontier.finitarySzemeredi_three` : the finitary statement for `k = 3`, deduced from Roth's
  theorem (available in Mathlib as `roth_3ap_theorem_nat`).
* `Frontier.furstenberg_szemeredi_three` : the resulting *unconditional* base case: every set of
  naturals of positive upper density contains a 3-term arithmetic progression.
-/

open Filter Finset

open scoped Classical

namespace Frontier

/-- `ContainsAP A k` says that `A` contains an arithmetic progression of length `k` with
positive common difference. -/
def ContainsAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

lemma ContainsAP.mono_set {A B : Set ℕ} {k : ℕ} (h : ContainsAP A k) (hAB : A ⊆ B) :
    ContainsAP B k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi => hAB (h i hi)⟩

lemma ContainsAP.mono_length {A : Set ℕ} {k l : ℕ} (h : ContainsAP A l) (hkl : k ≤ l) :
    ContainsAP A k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi => h i (hi.trans_le hkl)⟩

/-- The density of `A` inside `{0, 1, ..., n - 1}`. -/
noncomputable def densityUpTo (A : Set ℕ) (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun x => x ∈ A) |>.card : ℝ) / n

/-- The upper asymptotic density of a set of naturals. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ := limsup (densityUpTo A) atTop

lemma densityUpTo_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ densityUpTo A n := by
  unfold densityUpTo; positivity

lemma densityUpTo_le_one (A : Set ℕ) (n : ℕ) : densityUpTo A n ≤ 1 := by
  unfold densityUpTo
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)

/-- Sanity check: the whole of `ℕ` has upper density `1`, so the density hypothesis below is
not vacuous. -/
lemma upperDensity_univ : upperDensity Set.univ = 1 := by
  have h : densityUpTo Set.univ =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp [densityUpTo, Finset.filter_true_of_mem, hn'.ne']
  rw [upperDensity, limsup_congr h, limsup_const]

/-- Positive upper density implies that infinitely many initial segments have density bounded
below by a fixed positive constant. -/
lemma exists_frequently_density_ge {A : Set ℕ} (hA : 0 < upperDensity A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n ≥ N, 0 < n ∧
      δ * n ≤ (((Finset.range n).filter (fun x => x ∈ A)).card : ℝ) := by
  set δ := upperDensity A / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (densityUpTo A) := by
    refine ⟨0, fun a ha => ?_⟩
    rw [eventually_map] at ha
    obtain ⟨n, hn⟩ := ha.exists
    exact (densityUpTo_nonneg A n).trans hn
  have hlt : δ < limsup (densityUpTo A) atTop := by
    rw [← upperDensity]; linarith
  have hfreq : ∃ᶠ n in atTop, δ < densityUpTo A n :=
    Filter.frequently_lt_of_lt_limsup hcobdd hlt
  refine ⟨δ, hδ, fun N => ?_⟩
  obtain ⟨n, hnN, hn⟩ := (hfreq.and_eventually (eventually_ge_atTop N)).exists
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [densityUpTo] at hnN; linarith
    · exact hn0
  refine ⟨n, hn, hnpos, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  rw [densityUpTo, lt_div_iff₀ hn'] at hnN
  linarith

/-- The finitary form of Szemerédi's theorem for progressions of length `k`: for every positive
density `δ` there is an `N` such that every subset of `{0, ..., n - 1}` of size at least `δ * n`,
with `n ≥ N`, contains a `k`-term arithmetic progression. -/
def FinitarySzemeredi (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ B : Finset ℕ, B ⊆ Finset.range n →
    δ * n ≤ (B.card : ℝ) → ContainsAP (B : Set ℕ) k

/-- **Szemerédi's theorem** (Furstenberg's multiple recurrence formulation, reduced to its
finitary form): a set of naturals of positive upper density contains arithmetic progressions of
every length `k`, granted the finitary statement `FinitarySzemeredi k`.

The finitary hypothesis is unconditionally verified for `k ≤ 3` in
`Frontier.finitarySzemeredi_three`, which yields the unconditional base case
`Frontier.furstenberg_szemeredi_three`. -/
theorem furstenberg_szemeredi (k : ℕ) (hk : FinitarySzemeredi k) (A : Set ℕ)
    (hA : 0 < upperDensity A) : ContainsAP A k := by
  obtain ⟨δ, hδ, hfreq⟩ := exists_frequently_density_ge hA
  obtain ⟨N, hN⟩ := hk δ hδ
  obtain ⟨n, hnN, _, hcard⟩ := hfreq N
  have := hN n hnN ((Finset.range n).filter (fun x => x ∈ A)) (Finset.filter_subset _ _) hcard
  refine this.mono_set ?_
  intro x hx
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
  exact hx.2

/-- Failure of `ThreeAPFree` produces a genuine 3-term arithmetic progression with positive
common difference. -/
lemma containsAP_three_of_not_threeAPFree {s : Set ℕ} (h : ¬ ThreeAPFree s) :
    ContainsAP s 3 := by
  rw [ThreeAPFree] at h
  push_neg at h
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := h
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · refine ⟨a, b - a, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ha
    · have h1 : a + 1 * (b - a) = b := by omega
      rw [h1]; exact hb
    · have h2 : a + 2 * (b - a) = c := by omega
      rw [h2]; exact hc
  · refine ⟨c, b - c, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hc
    · have h1 : c + 1 * (b - c) = b := by omega
      rw [h1]; exact hb
    · have h2 : c + 2 * (b - c) = a := by omega
      rw [h2]; exact ha

/-- The finitary Szemerédi statement for `k = 3`, i.e. **Roth's theorem**. -/
theorem finitarySzemeredi_three : FinitarySzemeredi 3 := by
  intro δ hδ
  refine ⟨cornersTheoremBound (δ / 3), fun n hn B hB hcard => ?_⟩
  exact containsAP_three_of_not_threeAPFree (roth_3ap_theorem_nat δ hδ hn B hB hcard)

/-- **Unconditional base case**: every set of naturals of positive upper density contains a
3-term arithmetic progression. -/
theorem furstenberg_szemeredi_three (A : Set ℕ) (hA : 0 < upperDensity A) : ContainsAP A 3 :=
  furstenberg_szemeredi 3 finitarySzemeredi_three A hA

/-- Consequently, sets of positive upper density contain progressions of every length `k ≤ 3`. -/
theorem furstenberg_szemeredi_le_three (A : Set ℕ) (hA : 0 < upperDensity A) {k : ℕ}
    (hk : k ≤ 3) : ContainsAP A k :=
  (furstenberg_szemeredi_three A hA).mono_length hk

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

