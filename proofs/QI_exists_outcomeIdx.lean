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

/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QI

open Finset

/-! ## The PBR ontological model

An ontological (hidden variable) model for the two preparations
`|0⟩` (encoded by `false`) and `|+⟩` (encoded by `true`) of a qubit consists of:

* a set `Λ` of ontic states;
* for each preparation `b : Bool` a probability distribution `μ b` on `Λ`;
* a response function `ξ` for a joint measurement with four outcomes performed on two
  independently prepared systems: `ξ l₁ l₂ k` is the probability of outcome `k`
  when the two systems are in ontic states `l₁` and `l₂`.

The *preparation independence postulate* is built into the model: the ontic state of the
composite system is the pair `(l₁, l₂)` of the two individual ontic states, distributed
according to the product of the two marginals; hence the outcome probabilities are
obtained by averaging `ξ l₁ l₂ k` against the product distribution.

The field `zero_prob` records the quantum prediction for the PBR measurement: for each
pair `(b₁, b₂)` of preparations the outcome `outcomeIdx b₁ b₂` has probability zero,
because the corresponding measurement vector is orthogonal to the product state
`|b₁⟩ ⊗ |b₂⟩` (see `orthogonal_to_product` below).  Averaged against the product
distribution, a vanishing probability forces `ξ l₁ l₂ (outcomeIdx b₁ b₂) = 0` for all
`l₁, l₂` in the supports of `μ b₁` and `μ b₂`. -/

/-- The index of the measurement outcome that quantum mechanics forbids for the product
preparation `|b₁⟩ ⊗ |b₂⟩`. -/
def outcomeIdx (b₁ b₂ : Bool) : Fin 4 :=
  match b₁, b₂ with
  | false, false => 0
  | false, true  => 1
  | true,  false => 2
  | true,  true  => 3

/-- An ontological model of the PBR scenario, satisfying preparation independence and
reproducing the quantum zero-probability predictions for the PBR measurement. -/
structure PBRModel (Λ : Type*) [Fintype Λ] where
  /-- `μ b` is the ontic distribution associated with preparation `b`. -/
  μ : Bool → Λ → ℝ
  /-- `ξ l₁ l₂ k` is the probability of outcome `k` given the ontic pair `(l₁, l₂)`. -/
  ξ : Λ → Λ → Fin 4 → ℝ
  ξ_nonneg : ∀ l₁ l₂ k, 0 ≤ ξ l₁ l₂ k
  /-- The response function is normalised: some outcome always occurs. -/
  ξ_sum : ∀ l₁ l₂, ∑ k, ξ l₁ l₂ k = 1
  /-- Quantum prediction: outcome `outcomeIdx b₁ b₂` never occurs for the preparation
  `|b₁⟩ ⊗ |b₂⟩`; by preparation independence this must hold pointwise on the product of
  the supports. -/
  zero_prob : ∀ (b₁ b₂ : Bool) (l₁ l₂ : Λ),
    0 < μ b₁ l₁ → 0 < μ b₂ l₂ → ξ l₁ l₂ (outcomeIdx b₁ b₂) = 0

/-- Every index in `Fin 4` is the forbidden outcome of one of the four product
preparations. -/
lemma exists_outcomeIdx (k : Fin 4) : ∃ b₁ b₂ : Bool, outcomeIdx b₁ b₂ = k := by
  fin_cases k
  · exact ⟨false, false, rfl⟩
  · exact ⟨false, true, rfl⟩
  · exact ⟨true, false, rfl⟩
  · exact ⟨true, true, rfl⟩

/-- **Pusey–Barrett–Rudolph theorem.**  In any ontological model of the PBR scenario
satisfying preparation independence and reproducing the quantum zero-probability
predictions, the ontic distributions of the two distinct pure states `|0⟩` and `|+⟩`
have disjoint supports: no ontic state is compatible with both preparations.  In other
words the quantum state is *ontic*, not merely epistemic. -/
theorem pbr_theorem {Λ : Type*} [Fintype Λ] (M : PBRModel Λ) (l : Λ) :
    ¬ (0 < M.μ false l ∧ 0 < M.μ true l) := by
  rintro ⟨h0, h1⟩
  have hall : ∀ k : Fin 4, M.ξ l l k = 0 := by
    intro k
    obtain ⟨b₁, b₂, rfl⟩ := exists_outcomeIdx k
    cases b₁ <;> cases b₂
    · exact M.zero_prob false false l l h0 h0
    · exact M.zero_prob false true l l h0 h1
    · exact M.zero_prob true false l l h1 h0
    · exact M.zero_prob true true l l h1 h1
  have hsum : ∑ k, M.ξ l l k = 1 := M.ξ_sum l l
  rw [Finset.sum_congr rfl (fun k _ => hall k)] at hsum
  simp at hsum

/-! ## The model class is non-vacuous

A ψ-ontic model realising all the hypotheses: the ontic state simply records which of the
two preparations was used, and the response function is chosen to satisfy the quantum
constraints. -/

/-- A concrete PBR model on `Λ = Bool`, in which the ontic state records the preparation.
This shows that the hypotheses of `pbr_theorem` are consistent. -/
def onticModel : PBRModel Bool where
  μ b l := if b = l then 1 else 0
  ξ l₁ l₂ k := if k = outcomeIdx (!l₁) l₂ then 1 else 0
  ξ_nonneg := by intro l₁ l₂ k; positivity
  ξ_sum := by
    intro l₁ l₂
    rw [Finset.sum_ite_eq' Finset.univ (outcomeIdx (!l₁) l₂) (fun _ => (1 : ℝ))]
    simp
  zero_prob := by
    intro b₁ b₂ l₁ l₂ h₁ h₂
    have e₁ : b₁ = l₁ := by by_contra h; simp [h] at h₁
    have e₂ : b₂ = l₂ := by by_contra h; simp [h] at h₂
    subst e₁; subst e₂
    have : outcomeIdx b₁ b₂ ≠ outcomeIdx (!b₁) b₂ := by
      cases b₁ <;> cases b₂ <;> decide
    simp [this]

/-! ## The quantum input: the PBR measurement

We record the linear-algebraic fact underlying the hypothesis `zero_prob`.  Vectors of
`ℂ⁴` are written in the product basis `|00⟩, |01⟩, |10⟩, |11⟩`.  All vectors below are
unnormalised, which is irrelevant for orthogonality.  With `|0⟩ = (1,0)`,
`|1⟩ = (0,1)`, `|+⟩ = (1,1)`, `|-⟩ = (1,-1)` the four PBR measurement vectors are

* `mvec 0 = |01⟩ + |10⟩`,
* `mvec 1 = |0-⟩ + |1+⟩`,
* `mvec 2 = |+1⟩ + |-0⟩`,
* `mvec 3 = |+-⟩ + |-+⟩`,

and `mvec (outcomeIdx b₁ b₂)` is orthogonal to `|b₁⟩ ⊗ |b₂⟩`. -/

/-- The Hermitian inner product on `Fin 4 → ℂ`. -/
noncomputable def cdot (x y : Fin 4 → ℂ) : ℂ := ∑ i, star (x i) * y i

/-- The (unnormalised) product state `|b₁⟩ ⊗ |b₂⟩`, where `false ↦ |0⟩` and
`true ↦ |+⟩`. -/
def prodState (b₁ b₂ : Bool) : Fin 4 → ℂ :=
  match b₁, b₂ with
  | false, false => ![1, 0, 0, 0]
  | false, true  => ![1, 1, 0, 0]
  | true,  false => ![1, 0, 1, 0]
  | true,  true  => ![1, 1, 1, 1]

/-- The four (unnormalised) vectors of the PBR entangled measurement basis. -/
def mvec : Fin 4 → (Fin 4 → ℂ) :=
  ![![0, 1, 1, 0], ![1, -1, 1, 1], ![1, 1, -1, 1], ![2, 0, 0, -2]]

/-- The PBR measurement vectors are pairwise orthogonal, hence (being four nonzero
vectors in `ℂ⁴`) they form an orthogonal basis, i.e. a genuine projective measurement. -/
theorem mvec_orthogonal (j k : Fin 4) (h : j ≠ k) : cdot (mvec j) (mvec k) = 0 := by
  fin_cases j <;> fin_cases k <;> simp_all [cdot, mvec, Fin.sum_univ_four]

/-- Each PBR measurement vector is nonzero. -/
theorem mvec_ne_zero (k : Fin 4) : mvec k ≠ 0 := by
  intro h
  fin_cases k
  · exact absurd (congrFun h 1) (by simp [mvec])
  · exact absurd (congrFun h 0) (by simp [mvec])
  · exact absurd (congrFun h 0) (by simp [mvec])
  · exact absurd (congrFun h 0) (by simp [mvec])

/-- **The quantum input to the PBR argument.**  The measurement vector indexed by
`outcomeIdx b₁ b₂` is orthogonal to the product state `|b₁⟩ ⊗ |b₂⟩`; by the Born rule
that outcome has probability zero for that preparation. -/
theorem orthogonal_to_product (b₁ b₂ : Bool) :
    cdot (mvec (outcomeIdx b₁ b₂)) (prodState b₁ b₂) = 0 := by
  cases b₁ <;> cases b₂ <;>
    simp [cdot, mvec, prodState, outcomeIdx, Fin.sum_univ_four]

end QI

