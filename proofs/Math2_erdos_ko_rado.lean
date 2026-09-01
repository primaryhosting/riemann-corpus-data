/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

/-- **Erdős–Ko–Rado theorem**: a `k`-uniform intersecting family of subsets of an `n`-element
set with `n ≥ 2 * k` has at most `(n - 1).choose (k - 1)` members. -/
theorem erdos_ko_rado {n k : ℕ} (hn : 2 * k ≤ n) (𝒜 : Finset (Finset (Fin n)))
    (hsize : ∀ A ∈ 𝒜, A.card = k)
    (hinter : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  refine Finset.erdos_ko_rado (𝒜 := 𝒜) (r := k) ?_ ?_ ?_
  · intro A hA B hB hdisj
    have h := hinter A hA B hB
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    rw [hdisj] at h
    exact absurd h (by simp)
  · intro A hA
    exact hsize A hA
  · omega

end Math2

