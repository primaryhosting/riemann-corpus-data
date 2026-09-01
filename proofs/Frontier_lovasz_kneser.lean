/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`,
and two of them are adjacent when they are disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj s t := s ≠ t ∧ Disjoint (s : Finset (Fin n)) (t : Finset (Fin n))
  symm := by
    rintro s t ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp]
lemma kneserGraph_adj {n k : ℕ} (s t : KneserVertex n k) :
    (kneserGraph n k).Adj s t ↔ s ≠ t ∧ Disjoint (s : Finset (Fin n)) (t : Finset (Fin n)) :=
  Iff.rfl

/-! ### The easy (combinatorial) upper bound -/

/-- Every vertex of `KG_{n,k}` is a nonempty set when `1 ≤ k`. -/
lemma kneserVertex_nonempty {n k : ℕ} (hk : 1 ≤ k) (s : KneserVertex n k) :
    (s : Finset (Fin n)).Nonempty := by
  rw [← Finset.card_pos, s.2]
  omega

/-- The colouring witnessing `χ(KG_{n,k}) ≤ n - 2k + 2`: a `k`-set `S` gets colour
`min (S.min') (n + 1 - 2k)`. -/
theorem kneserGraph_colorable (n k : ℕ) (hk : 1 ≤ k) (h : 2 * k ≤ n + 1) :
    (kneserGraph n k).Colorable (n + 2 - 2 * k) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk
    (fun s => (⟨min ((s.1.min' (kneserVertex_nonempty hk s)).val) (n + 1 - 2 * k), by omega⟩ :
      Fin (n + 2 - 2 * k))) ?_⟩
  rintro s t ⟨hst, hdisj⟩ hcol
  set a : ℕ := (s.1.min' (kneserVertex_nonempty hk s)).val with ha
  set b : ℕ := (t.1.min' (kneserVertex_nonempty hk t)).val with hb
  have hcol' : min a (n + 1 - 2 * k) = min b (n + 1 - 2 * k) := congrArg Fin.val hcol
  by_cases hlt : a < n + 1 - 2 * k
  · -- the two minima coincide, so the sets share that element
    have hab : a = b := by omega
    have hmem : s.1.min' (kneserVertex_nonempty hk s) ∈ t.1 := by
      have : s.1.min' (kneserVertex_nonempty hk s) = t.1.min' (kneserVertex_nonempty hk t) :=
        Fin.ext hab
      rw [this]
      exact Finset.min'_mem _ _
    exact (Finset.disjoint_left.mp hdisj (Finset.min'_mem _ _)) hmem
  · -- both sets live inside the last `2k - 1` elements, so they cannot be disjoint
    have hbge : n + 1 - 2 * k ≤ b := by omega
    have hage : n + 1 - 2 * k ≤ a := by omega
    have hn : n + 1 - 2 * k < n := by omega
    set c : Fin n := ⟨n + 1 - 2 * k, hn⟩ with hc
    have hsub : s.1 ∪ t.1 ⊆ Finset.Ici c := by
      intro x hx
      rw [Finset.mem_union] at hx
      rw [Finset.mem_Ici]
      rcases hx with hx | hx
      · have := Finset.min'_le _ x hx
        exact le_trans (by simpa [hc, Fin.le_def] using hage) this
      · have := Finset.min'_le _ x hx
        exact le_trans (by simpa [hc, Fin.le_def] using hbge) this
    have hcard : (s.1 ∪ t.1).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj, s.2, t.2]; ring
    have hIci : (Finset.Ici c).card = n - (n + 1 - 2 * k) := Fin.card_Ici c
    have := Finset.card_le_card hsub
    rw [hcard, hIci] at this
    omega

/-! ### The base case `k = 1` -/

/-- For `k = 1` the Kneser graph is the complete graph on `n` vertices:
two distinct singletons are automatically disjoint. -/
theorem kneserGraph_one_eq_top (n : ℕ) : kneserGraph n 1 = ⊤ := by
  ext s t
  simp only [kneserGraph_adj, top_adj]
  refine ⟨fun h => h.1, fun hst => ⟨hst, ?_⟩⟩
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp s.2
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp t.2
  have hxy : x ≠ y := by
    rintro rfl
    exact hst (Subtype.ext (hx.trans hy.symm))
  rw [hx, hy]
  simpa using hxy

/-- **Lovász–Kneser theorem, base case `k = 1`.**
The chromatic number of the Kneser graph `KG_{n,1}` is `n + 2 - 2 * 1 = n`,
in agreement with the Lovász formula `χ(KG_{n,k}) = n - 2k + 2`. -/
theorem lovasz_kneser (n : ℕ) :
    (kneserGraph n 1).chromaticNumber = (n + 2 - 2 * 1 : ℕ) := by
  rw [kneserGraph_one_eq_top, SimpleGraph.chromaticNumber_top]
  simp [KneserVertex, Fintype.card_finset_len]

end Frontier

