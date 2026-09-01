import Mathlib

open Finset Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Math

/-- The sum of all `n`-th roots of unity in `ℂ` is `0`, for `1 < n`. -/
lemma sum_nthRootsFinset_eq_zero {n : ℕ} (hn : 1 < n) :
    ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ζ = 0 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n :=
    ⟨_, Complex.isPrimitiveRoot_exp n (by omega)⟩
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) (Finset.range n) := by
    intro i hi j hj h
    exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  have himg : Finset.image (fun i : ℕ => ζ ^ i) (Finset.range n) = nthRootsFinset n (1 : ℂ) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Polynomial.mem_nthRootsFinset (by omega), ← pow_mul, mul_comm, pow_mul,
        hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← himg, Finset.sum_image (fun i hi j hj h => hinj hi hj h)]
  exact hζ.geom_sum_eq_zero hn

/-- The sum over the divisors of `n` of the sums of the primitive `d`-th roots of unity
equals the sum of all `n`-th roots of unity. -/
lemma sum_divisors_sum_primitiveRoots (n : ℕ) :
    ∑ d ∈ n.divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ = ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ζ := by
  classical
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, Finset.sum_biUnion]
  intro i _ j _ hij
  exact IsPrimitiveRoot.disjoint hij

/-- The sum of the primitive `9`-th roots of unity equals `μ 9` (which is `0`). -/
theorem mobius_root_sum_9 : ∑ ζ ∈ primitiveRoots 9 ℂ, ζ = (μ 9 : ℂ) := by
  have h9 : ∑ d ∈ (9 : ℕ).divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ = 0 := by
    rw [sum_divisors_sum_primitiveRoots]
    exact sum_nthRootsFinset_eq_zero (by norm_num)
  have h3 : ∑ d ∈ (3 : ℕ).divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ = 0 := by
    rw [sum_divisors_sum_primitiveRoots]
    exact sum_nthRootsFinset_eq_zero (by norm_num)
  have e9 : (9 : ℕ).divisors = {1, 3, 9} := by decide
  have e3 : (3 : ℕ).divisors = {1, 3} := by decide
  rw [e9] at h9
  rw [e3] at h3
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at h9
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h3
  have hmu : (μ 9 : ℂ) = 0 := by
    have hns : ¬ Squarefree (9 : ℕ) := by
      intro h
      have h3 := h 3 ⟨1, by norm_num⟩
      rw [Nat.isUnit_iff] at h3
      omega
    have : μ 9 = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
    rw [this]
    norm_num
  rw [hmu]
  linear_combination h9 - h3

end Math

