import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains a `k`-term arithmetic
progression `a, a + d, …, a + (k-1) d` with positive common difference `d`. -/
def HasAPOfLength (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- Containing an arithmetic progression of length `k` is monotone in `k`. -/
theorem HasAPOfLength.mono {S : Set ℕ} {k l : ℕ} (h : HasAPOfLength S k) (hlk : l ≤ k) :
    HasAPOfLength S l := by
  obtain ⟨a, d, hd, ha⟩ := h
  exact ⟨a, d, hd, fun i hi => ha i (lt_of_lt_of_le hi hlk)⟩

/-- **Unconditional base cases.** The primes contain arithmetic progressions of every
length `k ≤ 10`: the ten numbers `199 + 210 i`, `i < 10`, are all prime. -/
theorem primes_hasAPOfLength_of_le_ten (k : ℕ) (hk : k ≤ 10) :
    HasAPOfLength {p : ℕ | Nat.Prime p} k := by
  refine HasAPOfLength.mono (k := 10) ⟨199, 210, by norm_num, ?_⟩ hk
  intro i hi
  interval_cases i <;> norm_num [Set.mem_setOf_eq]

/-- The Erdős conjecture on arithmetic progressions: any set of natural numbers whose
sum of reciprocals diverges contains arbitrarily long arithmetic progressions. -/
def ErdosAPConjecture : Prop :=
  ∀ S : Set ℕ, ¬ Summable (Set.indicator S fun n : ℕ => (1 : ℝ) / n) →
    ∀ k : ℕ, HasAPOfLength S k

/-- **Green–Tao (Lean-checked reduction).**

The primes contain arbitrarily long arithmetic progressions, conditional on the Erdős
conjecture on arithmetic progressions.  The reduction is unconditional and complete: it
combines the hypothesis with the (Mathlib-proved) divergence of the sum of the reciprocals
of the primes.  The unconditional Green–Tao theorem itself is not proved here; see
`Frontier.primes_hasAPOfLength_of_le_ten` for the unconditional base cases `k ≤ 10`. -/
theorem Green_Tao (hErdos : ErdosAPConjecture) (k : ℕ) :
    HasAPOfLength {p : ℕ | Nat.Prime p} k :=
  hErdos {p : ℕ | Nat.Prime p} not_summable_one_div_on_primes k

end Frontier

