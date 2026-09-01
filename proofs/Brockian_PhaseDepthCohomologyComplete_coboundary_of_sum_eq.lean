import Mathlib

/-!
# Coboundary Of Sum Eq
Category: B Brockian Frontier
Target: Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PhaseDepthCohomologyComplete

/-- A function on the 5-cycle `ZMod 5` whose total sum vanishes is a coboundary:
`g j = h (j + 1) - h j` for the partial-sum function `h`. -/
theorem exists_eq_coboundary_of_sum_eq_zero {G : Type*} [AddCommGroup G] (g : ZMod 5 → G)
    (hsum : g 0 + g 1 + g 2 + g 3 + g 4 = 0) :
    ∃ h : ZMod 5 → G, ∀ j, g j = h (j + 1) - h j := by
  refine ⟨fun k => if k = 1 then g 0 else if k = 2 then g 0 + g 1 else
      if k = 3 then g 0 + g 1 + g 2 else if k = 4 then g 0 + g 1 + g 2 + g 3 else 0, ?_⟩
  intro j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [show ((0:ZMod 5) + 1) = 1 from by decide, show ((1:ZMod 5) + 1) = 2 from by decide,
      show ((2:ZMod 5) + 1) = 3 from by decide, show ((3:ZMod 5) + 1) = 4 from by decide,
      show ((5:ZMod 5)) ≠ 1 from by decide, show ((5:ZMod 5)) ≠ 2 from by decide,
      show ((5:ZMod 5)) ≠ 3 from by decide, show ((5:ZMod 5)) ≠ 4 from by decide,
      show ((2:ZMod 5)) ≠ 1 from by decide, show ((3:ZMod 5)) ≠ 1 from by decide,
      show ((4:ZMod 5)) ≠ 1 from by decide, show ((3:ZMod 5)) ≠ 2 from by decide,
      show ((4:ZMod 5)) ≠ 2 from by decide, show ((4:ZMod 5)) ≠ 3 from by decide,
      show ((0:ZMod 5)) ≠ 1 from by decide, show ((0:ZMod 5)) ≠ 2 from by decide,
      show ((0:ZMod 5)) ≠ 3 from by decide, show ((0:ZMod 5)) ≠ 4 from by decide]
  all_goals first
    | abel
    | linear_combination (norm := abel) hsum

/-- **Completeness of the discrete cohomology no-go on the 5-cycle.**
If `c1 c2 : ZMod 5 → G` have equal total sums, then their difference is a coboundary:
there is `h : ZMod 5 → G` with `c1 j - c2 j = h (j + 1) - h j` for all `j`. -/
theorem coboundary_of_sum_eq {G : Type*} [AddCommGroup G] (c1 c2 : ZMod 5 → G)
    (hs : (Finset.univ.sum c1) = (Finset.univ.sum c2)) :
    ∃ h : ZMod 5 → G, ∀ j, c1 j - c2 j = h (j + 1) - h j := by
  have hsum : (c1 0 - c2 0) + (c1 1 - c2 1) + (c1 2 - c2 2) + (c1 3 - c2 3) + (c1 4 - c2 4) = 0 := by
    have h0 : ∑ j : ZMod 5, (c1 j - c2 j) = 0 := by
      simp only [Finset.sum_sub_distrib, hs, sub_self]
    have h1 : ∑ j : Fin 5, (c1 j - c2 j) = 0 := h0
    rw [Fin.sum_univ_five] at h1
    convert h1 using 3
  exact exists_eq_coboundary_of_sum_eq_zero (fun j => c1 j - c2 j) hsum

end Brockian.PhaseDepthCohomologyComplete

