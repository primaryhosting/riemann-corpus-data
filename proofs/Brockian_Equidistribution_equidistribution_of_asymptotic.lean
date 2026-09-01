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

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

open Filter Topology

namespace Brockian.Equidistribution

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` is `< c`. -/
noncomputable def countLT (x : ℕ → ℝ) (N : ℕ) (c : ℝ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (x n) < c).card

/-- The number of indices `n < N` whose fractional part lies in `[a, b)`. -/
noncomputable def countIco (x : ℕ → ℝ) (N : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card

/-- The empirical distribution function of the first `N` terms. -/
noncomputable def edf (x : ℕ → ℝ) (N : ℕ) (c : ℝ) : ℝ := (countLT x N c : ℝ) / N

lemma countLT_mono (x : ℕ → ℝ) (N : ℕ) {c c' : ℝ} (h : c ≤ c') :
    countLT x N c ≤ countLT x N c' := by
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, lt_of_lt_of_le hn.2 h⟩

lemma countLT_le (x : ℕ → ℝ) (N : ℕ) (c : ℝ) : countLT x N c ≤ N := by
  simpa using Finset.card_filter_le (Finset.range N) (fun n => Int.fract (x n) < c)

lemma edf_nonneg (x : ℕ → ℝ) (N : ℕ) (c : ℝ) : 0 ≤ edf x N c :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma edf_le_one (x : ℕ → ℝ) (N : ℕ) (c : ℝ) : edf x N c ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [edf, hN]
  · rw [edf, div_le_one (by exact_mod_cast hN)]
    exact_mod_cast countLT_le x N c

lemma edf_mono (x : ℕ → ℝ) (N : ℕ) {c c' : ℝ} (h : c ≤ c') : edf x N c ≤ edf x N c' := by
  unfold edf
  gcongr
  exact_mod_cast countLT_mono x N h

/-- Splitting the count below `b` into the count below `a` and the count in `[a, b)`. -/
lemma countLT_add_countIco (x : ℕ → ℝ) (N : ℕ) {a b : ℝ} (hab : a ≤ b) :
    countLT x N a + countIco x N a b = countLT x N b := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.range N).filter fun n => Int.fract (x n) < b)
    (p := fun n => Int.fract (x n) < a)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have h1 : ((Finset.range N).filter
      fun n => Int.fract (x n) < b ∧ Int.fract (x n) < a)
      = (Finset.range N).filter fun n => Int.fract (x n) < a := by
    apply Finset.filter_congr
    intro n _
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨lt_of_lt_of_le h hab, h⟩
  have h2 : ((Finset.range N).filter
      fun n => Int.fract (x n) < b ∧ ¬ Int.fract (x n) < a)
      = (Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b := by
    apply Finset.filter_congr
    intro n _
    simp only [Set.mem_Ico, not_lt]
    exact and_comm
  rw [h1, h2] at h
  exact h

/-- **Pointwise equidistribution.**  If the empirical distribution function converges to `c`
for every level `c` in a dense set `D`, then it converges to `c` for *every* `c ∈ [0,1]`. -/
lemma tendsto_edf_of_dense (x : ℕ → ℝ) (D : Set ℝ) (hD : Dense D)
    (hasym : ∀ c ∈ D, 0 ≤ c → c ≤ 1 → Tendsto (fun N => edf x N c) atTop (𝓝 c))
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Tendsto (fun N => edf x N c) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlow : ∀ᶠ N in atTop, c - ε < edf x N c := by
    rcases lt_or_ge (c - ε) 0 with h | h
    · filter_upwards with N using lt_of_lt_of_le h (edf_nonneg x N c)
    · obtain ⟨d, hdD, hd⟩ := hD.exists_between (show c - ε < c by linarith)
      have hd0 : (0:ℝ) ≤ d := le_of_lt (lt_of_le_of_lt h hd.1)
      have hd1 : d ≤ 1 := le_trans hd.2.le hc1
      have hev := (hasym d hdD hd0 hd1).eventually_const_lt hd.1
      filter_upwards [hev] with N hN
      exact lt_of_lt_of_le hN (edf_mono x N hd.2.le)
  have hhigh : ∀ᶠ N in atTop, edf x N c < c + ε := by
    rcases lt_or_ge 1 (c + ε) with h | h
    · filter_upwards with N using lt_of_le_of_lt (edf_le_one x N c) h
    · obtain ⟨d, hdD, hd⟩ := hD.exists_between (show c < c + ε by linarith)
      have hd0 : (0:ℝ) ≤ d := le_of_lt (lt_of_le_of_lt hc0 hd.1)
      have hd1 : d ≤ 1 := le_trans hd.2.le h
      have hev := (hasym d hdD hd0 hd1).eventually_lt_const hd.2
      filter_upwards [hev] with N hN
      exact lt_of_le_of_lt (edf_mono x N hd.1.le) hN
  obtain ⟨N₀, hN₀⟩ := (hlow.and hhigh).exists_forall_of_atTop
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h1, h2⟩ := hN₀ N hN
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-- **Equidistribution from asymptotics on a dense set of levels.**

Let `x : ℕ → ℝ` be a sequence.  Assume that for every level `c` in a dense set `D ⊆ ℝ`
with `0 ≤ c ≤ 1`, the proportion of the first `N` terms whose fractional part is `< c`
tends to `c`.  Then the sequence is equidistributed modulo one: for every subinterval
`[a, b) ⊆ [0, 1]`, the proportion of the first `N` terms whose fractional part lies in
`[a, b)` tends to `b - a`. -/
theorem equidistribution_of_asymptotic (x : ℕ → ℝ) (D : Set ℝ) (hD : Dense D)
    (hasym : ∀ c ∈ D, 0 ≤ c → c ≤ 1 → Tendsto (fun N => edf x N c) atTop (𝓝 c))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N => (countIco x N a b : ℝ) / N) atTop (𝓝 (b - a)) := by
  have hb0 : (0:ℝ) ≤ b := le_trans ha hab
  have ha1 : a ≤ 1 := le_trans hab hb
  have hta := tendsto_edf_of_dense x D hD hasym ha ha1
  have htb := tendsto_edf_of_dense x D hD hasym hb0 hb
  have key : ∀ N : ℕ, (countIco x N a b : ℝ) / N = edf x N b - edf x N a := by
    intro N
    have h := countLT_add_countIco x N hab
    have : (countIco x N a b : ℝ) = (countLT x N b : ℝ) - (countLT x N a : ℝ) := by
      have : ((countLT x N a + countIco x N a b : ℕ) : ℝ) = ((countLT x N b : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
      push_cast at this
      linarith
    rw [this, edf, edf, sub_div]
  simpa only [key] using htb.sub hta

end Brockian.Equidistribution

