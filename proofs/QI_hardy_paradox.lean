import Mathlib
/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory

namespace QI

/-- **Hardy's paradox, deterministic (local hidden variable) form.**

In a local realistic model, each hidden variable `l : Λ` deterministically fixes the outcomes
`a 1 l, a 2 l` of Alice's two possible measurement settings and `b 1 l, b 2 l` of Bob's.
The four Hardy conditions

* some run has `a₁ = b₁ = 1` (this is the positive-probability event),
* never `a₁ = 1` and `b₂ = 1`,
* never `a₂ = 1` and `b₁ = 1`,
* always `a₂ = 1` or `b₂ = 1`,

are jointly contradictory: no local hidden variable assignment can reproduce them. -/
theorem hardy_paradox_deterministic {Λ : Type*} (a₁ a₂ b₁ b₂ : Λ → Bool)
    (hpos : ∃ l, a₁ l = true ∧ b₁ l = true)
    (h₁ : ∀ l, ¬(a₁ l = true ∧ b₂ l = true))
    (h₂ : ∀ l, ¬(a₂ l = true ∧ b₁ l = true))
    (h₃ : ∀ l, a₂ l = true ∨ b₂ l = true) :
    False := by
  obtain ⟨l, ha, hb⟩ := hpos
  rcases h₃ l with h | h
  · exact h₂ l ⟨h, hb⟩
  · exact h₁ l ⟨ha, h⟩

/-- **Hardy's paradox (measure-theoretic / probabilistic form).**

Let `μ` be any measure on a sample space `Ω` (e.g. a probability measure describing the runs of
the experiment), and let `A₁, A₂, B₁, B₂ ⊆ Ω` be the events "Alice's setting `i` yields outcome
`1`" and "Bob's setting `j` yields outcome `1`", as they would be given by a *local realistic*
model where all four outcomes are simultaneously defined on the same sample space.

Hardy's three "zero-probability" conditions

* `μ (A₁ ∩ B₂) = 0`,
* `μ (A₂ ∩ B₁) = 0`,
* `μ (A₂ᶜ ∩ B₂ᶜ) = 0`

force `μ (A₁ ∩ B₁) = 0`. Quantum mechanics, however, predicts a strictly positive fraction of
runs with `A₁ ∩ B₁` (about 9%), so no local realistic model can reproduce the quantum
predictions — a proof of nonlocality without inequalities.

No measurability assumptions are needed: the argument only uses monotonicity and subadditivity
of the outer measure. -/
theorem hardy_paradox {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A₁ A₂ B₁ B₂ : Set Ω)
    (h₁ : μ (A₁ ∩ B₂) = 0)
    (h₂ : μ (A₂ ∩ B₁) = 0)
    (h₃ : μ (A₂ᶜ ∩ B₂ᶜ) = 0) :
    μ (A₁ ∩ B₁) = 0 := by
  have hsub : A₁ ∩ B₁ ⊆ (A₁ ∩ B₂) ∪ (A₂ ∩ B₁) ∪ (A₂ᶜ ∩ B₂ᶜ) := by
    rintro x ⟨hx1, hx2⟩
    by_cases hA₂ : x ∈ A₂
    · exact Or.inl (Or.inr ⟨hA₂, hx2⟩)
    · by_cases hB₂ : x ∈ B₂
      · exact Or.inl (Or.inl ⟨hx1, hB₂⟩)
      · exact Or.inr ⟨hA₂, hB₂⟩
  refine measure_mono_null hsub ?_
  simp [measure_union_null_iff, h₁, h₂, h₃]

/-- **Hardy's paradox, contradiction form.**

If in addition a strictly positive fraction of the runs exhibits the event `A₁ ∩ B₁`
(as quantum mechanics predicts), the local realistic description is outright contradictory. -/
theorem hardy_paradox_pos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A₁ A₂ B₁ B₂ : Set Ω)
    (hpos : 0 < μ (A₁ ∩ B₁))
    (h₁ : μ (A₁ ∩ B₂) = 0)
    (h₂ : μ (A₂ ∩ B₁) = 0)
    (h₃ : μ (A₂ᶜ ∩ B₂ᶜ) = 0) :
    False :=
  absurd (hardy_paradox μ A₁ A₂ B₁ B₂ h₁ h₂ h₃) hpos.ne'

end QI

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

