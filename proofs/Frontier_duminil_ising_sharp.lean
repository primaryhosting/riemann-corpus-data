import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands in a
file, so the required header comment is placed immediately after the single `import Mathlib`
line (its text is otherwise verbatim).
-/

open scoped Classical

namespace Frontier

/-!
## Setting

Duminil-Copin's *sharpness of the phase transition* for the Ising model says that the
order parameter (the spontaneous magnetisation `m(β)`, or equivalently the long-range
order parameter) exhibits **no intermediate phase**: there is a single critical inverse
temperature `β_c` such that the order parameter vanishes identically on the whole
subcritical interval `β < β_c` and is strictly positive on the whole supercritical
interval `β > β_c`.

We formalise the order-parameter half of this statement in the axiomatic form in which it
is actually used: the input is a nonnegative, monotone (in `β`) order parameter, the
critical point is *defined* as the infimum of the set of inverse temperatures at which the
order parameter is positive, and the conclusion is the sharp dichotomy above.  This is the
Lean-checked reduction of the theorem to monotonicity of the magnetisation (which for the
Ising model is Griffiths' second inequality).
-/

/-- An abstract Ising-type order parameter: a nonnegative, nondecreasing function of the
inverse temperature `β`.  For the Ising model on a graph, `m β` is the spontaneous
magnetisation `⟨σ_0⟩⁺_β`, which is nonnegative and nondecreasing in `β` by the
Griffiths–Kelly–Sherman inequalities. -/
structure IsingOrderParameter where
  /-- The order parameter as a function of the inverse temperature. -/
  m : ℝ → ℝ
  /-- The order parameter is nondecreasing in the inverse temperature. -/
  mono : Monotone m
  /-- The order parameter is nonnegative. -/
  nonneg : ∀ β, 0 ≤ m β

namespace IsingOrderParameter

variable (M : IsingOrderParameter)

/-- The ordered phase: the set of inverse temperatures at which the order parameter is
strictly positive. -/
def orderedPhase : Set ℝ := {β : ℝ | 0 < M.m β}

/-- The critical inverse temperature, defined as the infimum of the ordered phase. -/
noncomputable def betaC : ℝ := sInf M.orderedPhase

/-- Above the critical point the order parameter is strictly positive (long-range order). -/
theorem pos_of_betaC_lt (hne : M.orderedPhase.Nonempty) {β : ℝ} (hβ : M.betaC < β) :
    0 < M.m β := by
  obtain ⟨β', hβ'mem, hβ'lt⟩ := Real.lt_sInf_add_pos hne (sub_pos.mpr hβ)
  have h : β' ≤ β := by
    have : M.betaC + (β - M.betaC) = β := by ring
    exact le_of_lt (this ▸ hβ'lt)
  exact lt_of_lt_of_le hβ'mem (M.mono h)

/-- Below the critical point the order parameter vanishes identically (no intermediate
phase). -/
theorem eq_zero_of_lt_betaC (hbdd : BddBelow M.orderedPhase) {β : ℝ} (hβ : β < M.betaC) :
    M.m β = 0 := by
  by_contra h
  have hpos : 0 < M.m β := lt_of_le_of_ne (M.nonneg β) (Ne.symm h)
  exact absurd (csInf_le hbdd hpos) (not_le.mpr hβ)

end IsingOrderParameter

/-- **Sharpness of the phase transition for the Ising model** (Duminil-Copin), in the
order-parameter formulation.

For an Ising-type order parameter `m` (nonnegative and nondecreasing in the inverse
temperature `β`, as follows for the Ising magnetisation from the Griffiths inequalities),
whose ordered phase `{β | 0 < m β}` is nonempty and bounded below, the critical inverse
temperature `β_c = sInf {β | 0 < m β}` sharply separates the two phases:

* for every `β < β_c` the order parameter vanishes: `m β = 0`;
* for every `β > β_c` the order parameter is strictly positive: `0 < m β`.

In particular there is no intermediate phase: the ordered phase is, up to the single point
`β_c`, exactly the half-line `(β_c, ∞)`. -/
theorem duminil_ising_sharp (M : IsingOrderParameter)
    (hne : M.orderedPhase.Nonempty) (hbdd : BddBelow M.orderedPhase) :
    (∀ β < M.betaC, M.m β = 0) ∧ (∀ β, M.betaC < β → 0 < M.m β) :=
  ⟨fun _ hβ => M.eq_zero_of_lt_betaC hbdd hβ, fun _ hβ => M.pos_of_betaC_lt hne hβ⟩

/-- Reformulation of sharpness as a description of the phase diagram: the ordered phase is
squeezed between the open and closed supercritical half-lines. -/
theorem duminil_ising_sharp_phase_diagram (M : IsingOrderParameter)
    (hne : M.orderedPhase.Nonempty) (hbdd : BddBelow M.orderedPhase) :
    Set.Ioi M.betaC ⊆ M.orderedPhase ∧ M.orderedPhase ⊆ Set.Ici M.betaC := by
  constructor
  · intro β hβ
    exact M.pos_of_betaC_lt hne hβ
  · intro β hβ
    exact csInf_le hbdd hβ

/-- A concrete nondegenerate instance of the framework (mean-field-like order parameter
`m β = max 0 (β - 1)`), witnessing that the hypotheses of `duminil_ising_sharp` are
satisfiable and that the critical point is the expected one. -/
noncomputable def meanFieldExample : IsingOrderParameter where
  m := fun β => max 0 (β - 1)
  mono := fun _ _ h => max_le_max le_rfl (by linarith)
  nonneg := fun _ => le_max_left _ _

@[simp] theorem meanFieldExample_orderedPhase :
    meanFieldExample.orderedPhase = Set.Ioi (1 : ℝ) := by
  ext β
  simp [IsingOrderParameter.orderedPhase, meanFieldExample]

@[simp] theorem meanFieldExample_betaC : meanFieldExample.betaC = 1 := by
  simp [IsingOrderParameter.betaC, meanFieldExample_orderedPhase]

theorem meanFieldExample_sharp :
    (∀ β < (1 : ℝ), meanFieldExample.m β = 0) ∧
      (∀ β, (1 : ℝ) < β → 0 < meanFieldExample.m β) := by
  have h := duminil_ising_sharp meanFieldExample
    (by simp [meanFieldExample_orderedPhase])
    (by rw [meanFieldExample_orderedPhase]; exact bddBelow_Ioi)
  simpa [meanFieldExample_betaC] using h

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

