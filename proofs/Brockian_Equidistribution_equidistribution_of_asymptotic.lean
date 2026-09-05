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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian
namespace Equidistribution

/-- `countIn u a b N` is the number of indices `n < N` for which the sequence value
`u n` lies in the half-open interval `[a, b)`. -/
noncomputable def countIn (u : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => a ≤ u n ∧ u n < b)).card

/-- Counting is additive along a splitting point: for `a ≤ b` and a nonnegative
sequence, the indices landing in `[0, b)` split into those in `[0, a)` and those in
`[a, b)`. -/
theorem countIn_split (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) {a b : ℝ}
    (hab : a ≤ b) (N : ℕ) :
    countIn u 0 b N = countIn u 0 a N + countIn u a b N := by
  classical
  unfold countIn
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range]
    constructor
    · rintro ⟨hn, -, hb⟩
      rcases lt_or_ge (u n) a with h | h
      · exact Or.inl ⟨hn, hu n, h⟩
      · exact Or.inr ⟨hn, h, hb⟩
    · rintro (⟨hn, -, hlt⟩ | ⟨hn, hge, hb⟩)
      · exact ⟨hn, hu n, lt_of_lt_of_le hlt hab⟩
      · exact ⟨hn, hu n, hb⟩
  · refine Finset.disjoint_left.mpr ?_
    intro n hn hn'
    simp only [Finset.mem_filter] at hn hn'
    exact absurd hn'.2.1 (not_le.mpr hn.2.2)

/-- **Equidistribution from the asymptotics on initial intervals.**

If the sequence `u` is nonnegative and, for every `c ∈ [0,1]`, the
proportion of the first `N` terms lying in `[0, c)` tends to `c`, then `u` is
equidistributed: for every subinterval `[a, b) ⊆ [0, 1]` the proportion of the first
`N` terms lying in `[a, b)` tends to its length `b - a`. -/
theorem equidistribution_of_asymptotic (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n)
    (hasymp : ∀ c ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun N : ℕ => (countIn u 0 c N : ℝ) / N) Filter.atTop (nhds c))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Filter.Tendsto (fun N : ℕ => (countIn u a b N : ℝ) / N) Filter.atTop
      (nhds (b - a)) := by
  have hA := hasymp a ⟨ha, le_trans hab hb⟩
  have hB := hasymp b ⟨le_trans ha hab, hb⟩
  have key : ∀ N : ℕ, (countIn u a b N : ℝ) / N
      = (countIn u 0 b N : ℝ) / N - (countIn u 0 a N : ℝ) / N := by
    intro N
    have h := countIn_split u hu hab N
    have : (countIn u 0 b N : ℝ) = (countIn u 0 a N : ℝ) + (countIn u a b N : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
    rw [this]
    ring
  simpa [key] using hB.sub hA

end Equidistribution
end Brockian

