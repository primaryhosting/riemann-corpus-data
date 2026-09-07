import Mathlib

/-! # No-go: the single-cycle phase-depth cocycle has no invariant beyond total depth.

On the single residue cycle `ZMod 5`, a roof function `c : ZMod 5 → G` drives the
phase-depth skew product `T(j, r) = (j + 1, r + c j)`. Two roofs are *cohomologous* (differ
by a coboundary `δh j = h (j+1) - h j`) exactly when they define gauge-equivalent
cocycles. This module proves the necessary half of the classification: **cohomologous
roofs share the same total depth** `∑ j, c j`. Total depth is therefore a genuine invariant
of the single-cycle construction — no gauge change can alter it.

Consequences: the total depth is the *only* additive invariant one can extract from a
single deterministic phase cycle (its converse — that equal total depth forces
cohomology, so total depth is a *complete* invariant — is the companion obligation). Any
genuinely new spectral content must therefore come from *branching* the cycle, where a
depth-holonomy invariant appears that residue-Fourier data cannot see (see
`Brockian.DepthHolonomySeparation`).
-/

namespace Brockian.PhaseDepthNoGo

variable {G : Type*} [AddCommGroup G]

/-- The discrete coboundary of a potential `h` on the residue cycle. -/
def coboundary (h : ZMod 5 → G) : ZMod 5 → G := fun j => h (j + 1) - h j

/-- Two roofs are cohomologous if they differ by a coboundary. -/
def Cohomologous (c₁ c₂ : ZMod 5 → G) : Prop :=
  ∃ h : ZMod 5 → G, ∀ j, c₁ j - c₂ j = coboundary h j

/-- Total depth of a roof: its sum over the cycle. -/
def totalDepth (c : ZMod 5 → G) : G := ∑ j, c j

/-- A coboundary sums to zero over the cycle (telescoping via the shift bijection
    `j ↦ j + 1`, which permutes `ZMod 5`). -/
theorem sum_coboundary (h : ZMod 5 → G) : ∑ j, coboundary h j = 0 := by
  unfold coboundary
  rw [Finset.sum_sub_distrib]
  have : ∑ j : ZMod 5, h (j + 1) = ∑ j : ZMod 5, h j :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod 5)) _ _ (fun j => rfl)
  rw [this, sub_self]

/-- **No-go (invariance).** Cohomologous roofs have equal total depth: total depth is a
    gauge invariant of the single-cycle phase-depth cocycle. -/
theorem totalDepth_eq_of_cohomologous {c₁ c₂ : ZMod 5 → G}
    (h : Cohomologous c₁ c₂) : totalDepth c₁ = totalDepth c₂ := by
  obtain ⟨φ, hφ⟩ := h
  have hsum : ∑ j, (c₁ j - c₂ j) = 0 := by
    simp_rw [hφ]; exact sum_coboundary φ
  rw [Finset.sum_sub_distrib] at hsum
  exact sub_eq_zero.mp hsum

/-- Constant roofs realize every total-depth value: total depth is a *surjective*
    invariant, so its fibers are exactly the gauge classes it can distinguish. -/
theorem totalDepth_const (g : G) : totalDepth (fun _ : ZMod 5 => g) = 5 • g := by
  simp [totalDepth, Finset.sum_const, Finset.card_univ]

end Brockian.PhaseDepthNoGo
