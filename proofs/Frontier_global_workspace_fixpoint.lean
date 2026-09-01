import Mathlib

/-!
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Classical

/-- A **global workspace** on a finite state lattice `α`: a broadcast operator
`bc : α → α` which is monotone (more information broadcast in, more information out). -/
structure GlobalWorkspace (α : Type*) [Fintype α] [Lattice α] [BoundedOrder α] where
  /-- The broadcast operator of the workspace. -/
  bc : α → α
  /-- Broadcasting is monotone. -/
  mono : Monotone bc

variable {α : Type*} [Fintype α] [Lattice α] [BoundedOrder α]

/-- `a` is a fixed point of the broadcast operator: a stable global workspace content. -/
def IsFixedPoint (W : GlobalWorkspace α) (a : α) : Prop := W.bc a = a

/-- `a` is a *least* fixed point of the broadcast operator. -/
def IsLeastFixedPoint (W : GlobalWorkspace α) (a : α) : Prop :=
  IsFixedPoint W a ∧ ∀ b, IsFixedPoint W b → a ≤ b

/-- The candidate least fixed point: the infimum of all pre-fixed points
(`b` with `bc b ≤ b`), taken over the finite state lattice. -/
noncomputable def lfpCandidate (W : GlobalWorkspace α) : α :=
  (Finset.univ.filter fun b => W.bc b ≤ b).inf id

lemma lfpCandidate_le_of_prefixed {W : GlobalWorkspace α} {b : α} (hb : W.bc b ≤ b) :
    lfpCandidate W ≤ b :=
  Finset.inf_le (f := id) (by simpa using hb)

lemma bc_lfpCandidate_le (W : GlobalWorkspace α) :
    W.bc (lfpCandidate W) ≤ lfpCandidate W := by
  refine Finset.le_inf ?_
  intro b hb
  have hb' : W.bc b ≤ b := by simpa using hb
  exact le_trans (W.mono (lfpCandidate_le_of_prefixed hb')) hb'

lemma le_bc_lfpCandidate (W : GlobalWorkspace α) :
    lfpCandidate W ≤ W.bc (lfpCandidate W) :=
  lfpCandidate_le_of_prefixed (W.mono (bc_lfpCandidate_le W))

/-- **Knaster–Tarski for a global workspace.**
A monotone broadcast operator on a finite state lattice has a least fixed point. -/
theorem global_workspace_fixpoint (W : GlobalWorkspace α) :
    ∃ a : α, IsLeastFixedPoint W a := by
  refine ⟨lfpCandidate W, le_antisymm (bc_lfpCandidate_le W) (le_bc_lfpCandidate W), ?_⟩
  intro b hb
  exact lfpCandidate_le_of_prefixed (le_of_eq hb)

end Frontier

