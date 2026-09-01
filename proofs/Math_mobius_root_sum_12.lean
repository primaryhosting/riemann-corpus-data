/-
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Math

/-- If `ζ` is a primitive 12-th root of unity in `ℂ`, then `ζ ^ 6 = -1`. -/
lemma pow_six_eq_neg_one_of_isPrimitiveRoot_twelve {ζ : ℂ} (h : IsPrimitiveRoot ζ 12) :
    ζ ^ 6 = -1 := by
  have h12 : (ζ ^ 6) ^ 2 = 1 := by
    rw [← pow_mul]
    simpa using h.pow_eq_one
  have hne : ζ ^ 6 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (ζ ^ 6 - 1) * (ζ ^ 6 + 1) = 0 := by linear_combination h12
  rcases mul_eq_zero.1 hfac with h1 | h2
  · exact absurd (sub_eq_zero.1 h1) hne
  · linear_combination h2

/-- The negation of a primitive 12-th root of unity is again a primitive 12-th root of unity. -/
lemma neg_mem_primitiveRoots_twelve {ζ : ℂ} (hζ : ζ ∈ primitiveRoots 12 ℂ) :
    -ζ ∈ primitiveRoots 12 ℂ := by
  have h : IsPrimitiveRoot ζ 12 := isPrimitiveRoot_of_mem_primitiveRoots hζ
  have h6 : ζ ^ 6 = -1 := pow_six_eq_neg_one_of_isPrimitiveRoot_twelve h
  have hpow : IsPrimitiveRoot (ζ ^ 7) 12 := h.pow_of_coprime 7 (by norm_num [Nat.Coprime])
  have h7 : ζ ^ 7 = -ζ := by linear_combination ζ * h6
  rw [h7] at hpow
  exact (mem_primitiveRoots (by norm_num)).2 hpow

/-- The sum of the primitive 12-th roots of unity equals `μ(12)`. -/
theorem mobius_root_sum_12 :
    ∑ ζ ∈ primitiveRoots 12 ℂ, ζ = (ArithmeticFunction.moebius 12 : ℂ) := by
  have hsq : ¬ Squarefree 12 := by
    intro h
    have h2 := h 2 ⟨3, by norm_num⟩
    rw [Nat.isUnit_iff] at h2
    norm_num at h2
  have hmu : ArithmeticFunction.moebius 12 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun a _ => -a) (fun a _ => by ring) ?_ ?_ ?_
  · intro a _ ha h
    exact ha (by linear_combination -h / 2)
  · intro a ha
    exact neg_mem_primitiveRoots_twelve ha
  · intro a _
    ring

end Math

