import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

variable {Ω : Type*} [DecidableEq Ω]

/-- `Frontier.IsInfoPartition I` says that `I : Ω → Finset Ω` assigns to each state `ω`
the cell of an information partition containing `ω`:  `ω` always belongs to its own cell,
and any two cells that meet are equal. -/
structure IsInfoPartition (I : Ω → Finset Ω) : Prop where
  self_mem : ∀ ω, ω ∈ I ω
  cell_eq : ∀ ω ω', ω' ∈ I ω → I ω' = I ω

/-- `Frontier.IsSelfEvident I C` says that the event `C` is *self-evident* (a union of cells)
for the information partition `I`: whenever the true state lies in `C`, the agent's information
cell is entirely contained in `C`. -/
def IsSelfEvident (I : Ω → Finset Ω) (C : Finset Ω) : Prop := ∀ ω ∈ C, I ω ⊆ C

/-- The prior probability (mass) of an event `S`, for a weight function `p`. -/
def prior (p : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ x ∈ S, p x

omit [DecidableEq Ω] in
@[simp] lemma prior_empty (p : Ω → ℝ) : prior p (∅ : Finset Ω) = 0 := by
  simp [prior]

/-- A self-evident event splits off one cell: `C \ I ω` is again self-evident. -/
lemma isSelfEvident_sdiff_cell {I : Ω → Finset Ω} (hI : IsInfoPartition I)
    {C : Finset Ω} (hC : IsSelfEvident I C) (ω : Ω) :
    IsSelfEvident I (C \ I ω) := by
  intro ω' hω'
  rw [Finset.mem_sdiff] at hω'
  obtain ⟨hω'C, hω'B⟩ := hω'
  intro x hx
  rw [Finset.mem_sdiff]
  refine ⟨hC ω' hω'C hx, ?_⟩
  intro hxB
  -- if the cell of `ω'` meets `I ω`, the two cells coincide, so `ω' ∈ I ω`, a contradiction
  have h1 : I x = I ω' := hI.cell_eq ω' x hx
  have h2 : I x = I ω := hI.cell_eq ω x hxB
  have h3 : I ω' = I ω := by rw [← h1, h2]
  exact hω'B (h3 ▸ hI.self_mem ω')

/-- **Averaging over a self-evident event.**  If an agent with information partition `I`
assigns, at every state of a self-evident event `C`, the same posterior value `a` to the
event `E`, then the prior conditional probability of `E` given `C` is also `a`
(stated in the multiplied-out form `prior (E ∩ C) = a * prior C`). -/
theorem prior_inter_of_isSelfEvident {p : Ω → ℝ} {E : Finset Ω} {I : Ω → Finset Ω}
    (hI : IsInfoPartition I) (a : ℝ) :
    ∀ C : Finset Ω, IsSelfEvident I C →
      (∀ ω ∈ C, prior p (E ∩ I ω) = a * prior p (I ω)) →
      prior p (E ∩ C) = a * prior p C := by
  intro C
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    intro hSE hpost
    rcases C.eq_empty_or_nonempty with rfl | ⟨ω, hω⟩
    · simp
    · have hBC : I ω ⊆ C := hSE ω hω
      have hωB : ω ∈ I ω := hI.self_mem ω
      have hlt : C \ I ω ⊂ C := by
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro hsub
        have := hsub hω
        rw [Finset.mem_sdiff] at this
        exact this.2 hωB
      have hSE' : IsSelfEvident I (C \ I ω) := isSelfEvident_sdiff_cell hI hSE ω
      have hpost' : ∀ ω' ∈ C \ I ω, prior p (E ∩ I ω') = a * prior p (I ω') := by
        intro ω' hω'
        exact hpost ω' (Finset.mem_sdiff.mp hω').1
      have hrec : prior p (E ∩ (C \ I ω)) = a * prior p (C \ I ω) := ih _ hlt hSE' hpost'
      -- split the sums over `C = I ω ∪ (C \ I ω)`
      have hsplit : prior p (C \ I ω) + prior p (I ω) = prior p C := by
        simpa [prior] using Finset.sum_sdiff (f := p) hBC
      have hEsub : E ∩ I ω ⊆ E ∩ C := Finset.inter_subset_inter_left hBC
      have hEeq : (E ∩ C) \ (E ∩ I ω) = E ∩ (C \ I ω) := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
      have hsplitE : prior p (E ∩ (C \ I ω)) + prior p (E ∩ I ω) = prior p (E ∩ C) := by
        have := Finset.sum_sdiff (f := p) hEsub
        rw [hEeq] at this
        simpa [prior] using this
      rw [← hsplitE, hrec, hpost ω hω, ← hsplit]
      ring

/-- **Aumann's agreement theorem** (finite, combinatorial form).

Two agents share a common prior `p` on a state space `Ω` and have information partitions
`I₁`, `I₂`.  Suppose `C` is an event that is self-evident for both agents (this is exactly
common knowledge: at every state of `C`, each agent knows `C`), that `C` has positive prior
probability, and that at every state of `C` agent 1 assigns posterior `a` to the event `E`
while agent 2 assigns posterior `b`.  In other words, the posteriors `a` and `b` are common
knowledge on `C`.  Then `a = b`: the agents cannot agree to disagree. -/
theorem aumann_agreement {p : Ω → ℝ} {E C : Finset Ω} {I₁ I₂ : Ω → Finset Ω}
    (hI₁ : IsInfoPartition I₁) (hI₂ : IsInfoPartition I₂)
    (hC₁ : IsSelfEvident I₁ C) (hC₂ : IsSelfEvident I₂ C)
    (hpos : 0 < prior p C)
    {a b : ℝ}
    (ha : ∀ ω ∈ C, prior p (E ∩ I₁ ω) = a * prior p (I₁ ω))
    (hb : ∀ ω ∈ C, prior p (E ∩ I₂ ω) = b * prior p (I₂ ω)) :
    a = b := by
  have h1 : prior p (E ∩ C) = a * prior p C :=
    prior_inter_of_isSelfEvident hI₁ a C hC₁ ha
  have h2 : prior p (E ∩ C) = b * prior p C :=
    prior_inter_of_isSelfEvident hI₂ b C hC₂ hb
  have : a * prior p C = b * prior p C := by rw [← h1, h2]
  exact mul_right_cancel₀ (ne_of_gt hpos) this

/-! ### A concrete instance, showing the hypotheses are satisfiable

Four equally likely states, agent 1 observes whether the state is in `{0,1}` or `{2,3}`,
agent 2 observes whether the state is in `{0,2}` or `{1,3}`.  The event `E = {0,3}` has
posterior `1/2` for both agents at every state, and the whole space is common knowledge. -/

/-- Agent 1's information partition in the example: cells `{0,1}` and `{2,3}`. -/
def exI₁ : Fin 4 → Finset (Fin 4) := fun ω => if ω.val < 2 then {0, 1} else {2, 3}

/-- Agent 2's information partition in the example: cells `{0,2}` and `{1,3}`. -/
def exI₂ : Fin 4 → Finset (Fin 4) := fun ω => if ω.val % 2 = 0 then {0, 2} else {1, 3}

example :
    IsInfoPartition exI₁ ∧ IsInfoPartition exI₂ ∧
    IsSelfEvident exI₁ (Finset.univ : Finset (Fin 4)) ∧
    IsSelfEvident exI₂ (Finset.univ : Finset (Fin 4)) ∧
    0 < prior (fun _ : Fin 4 => (1 / 4 : ℝ)) Finset.univ ∧
    (∀ ω ∈ (Finset.univ : Finset (Fin 4)),
      prior (fun _ => (1 / 4 : ℝ)) (({0, 3} : Finset (Fin 4)) ∩ exI₁ ω)
        = (1 / 2 : ℝ) * prior (fun _ => (1 / 4 : ℝ)) (exI₁ ω)) ∧
    (∀ ω ∈ (Finset.univ : Finset (Fin 4)),
      prior (fun _ => (1 / 4 : ℝ)) (({0, 3} : Finset (Fin 4)) ∩ exI₂ ω)
        = (1 / 2 : ℝ) * prior (fun _ => (1 / 4 : ℝ)) (exI₂ ω)) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    fun ω _ => Finset.subset_univ _, fun ω _ => Finset.subset_univ _, ?_, ?_, ?_⟩
  · norm_num [prior]
  · intro ω _
    fin_cases ω <;> simp [prior, exI₁]
  · intro ω _
    fin_cases ω <;> simp [prior, exI₂]

end Frontier

