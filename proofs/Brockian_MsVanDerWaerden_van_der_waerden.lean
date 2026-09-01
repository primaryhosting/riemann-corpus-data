import Mathlib
namespace Brockian.MsVanDerWaerden

open Combinatorics Finset

/-- The set of "moving" coordinates of a combinatorial line. -/
private def movingSet {k : ℕ} {ι : Type} [Fintype ι] (l : Line (Fin k) ι) : Finset ι :=
  Finset.univ.filter (fun i => l.idxFun i = none)

/-- The constant part of the sum along a combinatorial line. -/
private def lineConst {k : ℕ} {ι : Type} [Fintype ι] (l : Line (Fin k) ι) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none), ((l.idxFun i).map Fin.val).getD 0

/-- Summing the coordinates of a point on a combinatorial line in `ι → Fin k` gives an
arithmetic progression in the parameter `x`. -/
private lemma line_sum_eq {k : ℕ} {ι : Type} [Fintype ι] (l : Line (Fin k) ι) (x : Fin k) :
    ∑ i, ((l x i : ℕ)) = lineConst l + (x : ℕ) * (movingSet l).card := by
  simp [lineConst, movingSet]
  rw [← Finset.sum_filter_add_sum_filter_not (p := fun i => l.idxFun i ≠ none)]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp at hi
    cases h : l.idxFun i <;> simp_all
  · simp only [not_not]
    have heq : ∀ i ∈ Finset.univ.filter (fun i => l.idxFun i = none),
        ((l.idxFun i).getD x : ℕ) = x := by
      intro i hi
      simp [Finset.mem_filter.mp hi]
    rw [Finset.sum_congr rfl heq, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The sum of the coordinates of a point of the hypercube `ι → Fin k` is at most
`Fintype.card ι * k`. -/
private lemma sum_coords_le {k : ℕ} {ι : Type} [Fintype ι] (v : ι → Fin k) :
    ∑ i, ((v i : ℕ)) ≤ Fintype.card ι * k := by
  calc ∑ i, ((v i : ℕ)) ≤ ∑ _i : ι, k := by
         apply Finset.sum_le_sum
         intro i _
         exact Nat.le_of_lt (Fin.is_lt (v i))
       _ = Fintype.card ι * k := by simp

/-- Van der Waerden's theorem: for any k and any r-coloring of the naturals, some monochromatic
    arithmetic progression of length k exists within a bounded window.

    (The hypotheses `0 < k` and `0 < r` are kept as stated, although the proof does not
    need them.) -/
theorem van_der_waerden (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    ∃ N : ℕ, ∀ c : ℕ → Fin r, ∃ a d : ℕ, 0 < d ∧
      (∀ i, i < k → a + i * d ≤ N) ∧
      (∀ i j, i < k → j < k → c (a + i * d) = c (a + j * d)) := by
  obtain ⟨ι, hfin, hι⟩ := Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  refine ⟨Fintype.card ι * k, fun c => ?_⟩
  obtain ⟨l, col, hl⟩ := hι (fun v => c (∑ i, ((v i : ℕ))))
  refine ⟨lineConst l, (movingSet l).card, ?_, ?_, ?_⟩
  · rw [Finset.card_pos]
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [movingSet, hi]⟩
  · intro i hi
    rw [← line_sum_eq l ⟨i, hi⟩]
    exact sum_coords_le _
  · intro i j hi hj
    rw [← line_sum_eq l ⟨i, hi⟩, ← line_sum_eq l ⟨j, hj⟩]
    exact (hl ⟨i, hi⟩).trans (hl ⟨j, hj⟩).symm

end Brockian.MsVanDerWaerden

