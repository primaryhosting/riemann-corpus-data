import Mathlib

/-! # Complete gauge classification of the single-cycle phase-depth cocycle.

This module **packages the exact classification theorem** for the pentagonal phase-depth
construction on one directed cycle `ZMod 5`, with fiber an arbitrary abelian group `G`:

`Cohomologous c₁ c₂  ↔  totalDepth c₁ = totalDepth c₂`.

The two halves were proved separately — the *necessity* (`⇒`, the "no-go") in
`Brockian.PhaseDepthNoGo`, and the *sufficiency* (`⇐`, the completeness/converse) in
`Brockian.PhaseDepthCohomologyComplete`. This module consolidates both into the single
biconditional so the headline is one theorem: **on one directed pentagonal cycle, total
holonomy (total depth `∑ j, c j`) is the complete gauge invariant** — it is preserved by
every gauge change, and it is the *only* thing preserved: equal total depth forces the two
roofs to be gauge-equivalent. Nothing finer than the total is invariant; anything finer
requires branching the cycle (see `Brockian.DepthHolonomySeparation`).

Kept self-contained (`import Mathlib`) to match the corpus's per-module AXLE attestation
model; the constituent proofs are reproduced verbatim from the two source modules.
-/

namespace Brockian.PhaseDepthClassification

variable {G : Type*} [AddCommGroup G]

/-- The discrete coboundary of a potential `h` on the residue cycle. -/
def coboundary (h : ZMod 5 → G) : ZMod 5 → G := fun j => h (j + 1) - h j

/-- Two roofs are cohomologous if they differ by a coboundary (gauge-equivalent cocycles). -/
def Cohomologous (c₁ c₂ : ZMod 5 → G) : Prop :=
  ∃ h : ZMod 5 → G, ∀ j, c₁ j - c₂ j = coboundary h j

/-- Total depth of a roof: its holonomy summed once around the cycle. -/
def totalDepth (c : ZMod 5 → G) : G := ∑ j, c j

/-- A coboundary sums to zero over the cycle (telescoping via the shift bijection). -/
theorem sum_coboundary (h : ZMod 5 → G) : ∑ j, coboundary h j = 0 := by
  unfold coboundary
  rw [Finset.sum_sub_distrib]
  have : ∑ j : ZMod 5, h (j + 1) = ∑ j : ZMod 5, h j :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod 5)) _ _ (fun j => rfl)
  rw [this, sub_self]

/-- **Necessity (`⇒`, the no-go).** Cohomologous roofs have equal total depth. -/
theorem totalDepth_eq_of_cohomologous {c₁ c₂ : ZMod 5 → G}
    (h : Cohomologous c₁ c₂) : totalDepth c₁ = totalDepth c₂ := by
  obtain ⟨φ, hφ⟩ := h
  have hsum : ∑ j, (c₁ j - c₂ j) = 0 := by
    simp_rw [hφ]; exact sum_coboundary φ
  rw [Finset.sum_sub_distrib] at hsum
  exact sub_eq_zero.mp hsum

/-- **Sufficiency (`⇐`, completeness).** Equal total depth forces cohomology: the difference
`g j = c₁ j - c₂ j` is a coboundary, with witness the partial-sum potential
(`h 0 = 0`, `h k = g 0 + ⋯ + g (k-1)`); the seam at `j = 4` closes because `∑ j, g j = 0`. -/
theorem cohomologous_of_totalDepth_eq {c₁ c₂ : ZMod 5 → G}
    (hs : totalDepth c₁ = totalDepth c₂) : Cohomologous c₁ c₂ := by
  have hs' : Finset.univ.sum c₁ = Finset.univ.sum c₂ := by
    simpa [totalDepth] using hs
  set g : ZMod 5 → G := fun j => c₁ j - c₂ j with hg
  have h0 : Finset.univ.sum g = 0 := by
    simp [hg, Finset.sum_sub_distrib, hs']
  have huniv : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
  have hzero : g 0 + g 1 + g 2 + g 3 + g 4 = 0 := by
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at h0
    simp only [hg] at h0 ⊢
    linear_combination (norm := abel) h0
  refine ⟨fun k => (![0, g 0, g 0 + g 1, g 0 + g 1 + g 2, g 0 + g 1 + g 2 + g 3] : Fin 5 → G) k, ?_⟩
  intro j
  show g j = _ - _
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

/-- **Complete gauge classification.** On one directed pentagonal cycle, total depth is the
*complete* gauge invariant: two roofs are cohomologous **iff** they have equal total depth. -/
theorem cohomologous_iff_totalDepth_eq {c₁ c₂ : ZMod 5 → G} :
    Cohomologous c₁ c₂ ↔ totalDepth c₁ = totalDepth c₂ :=
  ⟨totalDepth_eq_of_cohomologous, cohomologous_of_totalDepth_eq⟩

end Brockian.PhaseDepthClassification
