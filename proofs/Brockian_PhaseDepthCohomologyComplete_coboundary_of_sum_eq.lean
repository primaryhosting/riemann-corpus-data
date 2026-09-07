import Mathlib

namespace Brockian.PhaseDepthCohomologyComplete

/-- **Completeness half of the discrete-cohomology no-go on the 5-cycle.**
If `c1 c2 : ZMod 5 → G` have equal total sums, then their difference is a coboundary:
there is `h : ZMod 5 → G` with `c1 j - c2 j = h (j + 1) - h j` for every `j`.

The witness is the partial-sum function of `g j = c1 j - c2 j`
(`h 0 = 0`, `h 1 = g 0`, ..., `h 4 = g 0 + g 1 + g 2 + g 3`); the seam at `j = 4`
closes precisely because `∑ j, g j = 0`. -/
theorem coboundary_of_sum_eq {G : Type*} [AddCommGroup G] (c1 c2 : ZMod 5 → G)
    (hs : (Finset.univ.sum c1) = (Finset.univ.sum c2)) :
    ∃ h : ZMod 5 → G, ∀ j, c1 j - c2 j = h (j + 1) - h j := by
  set g : ZMod 5 → G := fun j => c1 j - c2 j with hg
  -- Total sum of `g` vanishes.
  have h0 : Finset.univ.sum g = 0 := by
    simp [hg, Finset.sum_sub_distrib, hs]
  -- Expand `∑_{ZMod 5} g` into the explicit five-term sum, staying in ZMod 5 numerals.
  have huniv : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
  have hzero : g 0 + g 1 + g 2 + g 3 + g 4 = 0 := by
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at h0
    simp only [hg] at h0 ⊢
    linear_combination (norm := abel) h0
  -- Partial-sum witness (ZMod 5 ≃ Fin 5 defeq lets us index by an `Fin 5` vector).
  refine ⟨fun k => (![0, g 0, g 0 + g 1, g 0 + g 1 + g 2, g 0 + g 1 + g 2 + g 3] : Fin 5 → G) k, ?_⟩
  intro j
  fin_cases j
  · show g 0 = g 0 - 0
    abel
  · show g 1 = (g 0 + g 1) - g 0
    abel
  · show g 2 = (g 0 + g 1 + g 2) - (g 0 + g 1)
    abel
  · show g 3 = (g 0 + g 1 + g 2 + g 3) - (g 0 + g 1 + g 2)
    abel
  · show g 4 = 0 - (g 0 + g 1 + g 2 + g 3)
    linear_combination (norm := abel) hzero

end Brockian.PhaseDepthCohomologyComplete
