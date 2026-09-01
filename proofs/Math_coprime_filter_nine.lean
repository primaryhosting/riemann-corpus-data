import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The set of exponents `i < 9` with `gcd i 9 = 1`. -/
lemma coprime_filter_nine :
    (Finset.range 9).filter (fun i => Nat.Coprime i 9) = ({1, 2, 4, 5, 7, 8} : Finset ℕ) := by
  decide

/-- The sum of the primitive `9`-th roots of unity, expressed as a sum of powers of a
fixed primitive root. -/
lemma sum_primitiveRoots_nine_eq_pow_sum {ζ : ℂ} (h : IsPrimitiveRoot ζ 9) :
    ∑ z ∈ primitiveRoots 9 ℂ, z
      = ∑ i ∈ (Finset.range 9).filter (fun i => Nat.Coprime i 9), ζ ^ i := by
  refine (Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ ?_).symm
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact (mem_primitiveRoots (by norm_num)).2 (h.pow_of_coprime a ha.2)
  · intro a ha b hb H
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    exact h.pow_inj ha.1 hb.1 H
  · intro z hz
    rw [mem_primitiveRoots (by norm_num), h.isPrimitiveRoot_iff] at hz
    obtain ⟨i, hi, hic, rfl⟩ := hz
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hic⟩, rfl⟩
  · intro a _
    rfl

/-- The sum of the primitive 9-th roots of unity equals `μ(9) = 0`. -/
theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = (ArithmeticFunction.moebius 9 : ℂ) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 9)) 9 :=
    Complex.isPrimitiveRoot_exp 9 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)
  have h3 : IsPrimitiveRoot (ζ ^ 3) 3 := h.pow (by norm_num) (by norm_num)
  have g9 : ∑ i ∈ Finset.range 9, ζ ^ i = 0 := h.geom_sum_eq_zero (by norm_num)
  have g3 : ∑ i ∈ Finset.range 3, (ζ ^ 3) ^ i = 0 := h3.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← pow_mul] at g9 g3
  have hmu : (ArithmeticFunction.moebius 9 : ℂ) = 0 := by
    have : ArithmeticFunction.moebius 9 = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by
        intro hsq
        have := hsq 3 ⟨1, by norm_num⟩
        rw [Nat.isUnit_iff] at this
        norm_num at this)
    rw [this]
    norm_num
  rw [hmu, sum_primitiveRoots_nine_eq_pow_sum h, coprime_filter_nine]
  norm_num [Finset.sum_insert, Finset.mem_insert]
  linear_combination g9 - g3

end Math

